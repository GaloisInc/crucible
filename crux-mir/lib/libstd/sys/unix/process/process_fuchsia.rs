use crate::convert::TryInto;
use crate::fmt;
use crate::io;
use crate::mem;
use crate::ptr;

use crate::sys::process::process_common::*;
use crate::sys::process::zircon::{zx_handle_t, Handle};

use libc::{c_int, size_t};

////////////////////////////////////////////////////////////////////////////////
// Command
////////////////////////////////////////////////////////////////////////////////

impl Command {
    pub fn spawn(
        &mut self,
        default: Stdio,
        needs_stdin: bool,
    ) -> io::Result<(Process, StdioPipes)> {
        let envp = self.capture_env();

        if self.saw_nul() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "nul byte found in provided data",
            ));
        }

        let (ours, theirs) = self.setup_io(default, needs_stdin)?;

        let process_handle = unsafe { self.do_exec(theirs, envp.as_ref())? };

        Ok((Process { handle: Handle::new(process_handle) }, ours))
    }

    pub fn exec(&mut self, default: Stdio) -> io::Error {
        if self.saw_nul() {
            return io::Error::new(io::ErrorKind::InvalidInput, "nul byte found in provided data");
        }

        match self.setup_io(default, true) {
            Ok((_, _)) => {
                // FIXME: This is tough because we don't support the exec syscalls
                unimplemented!();
            }
            Err(e) => e,
        }
    }

    unsafe fn do_exec(
        &mut self,
        stdio: ChildPipes,
        maybe_envp: Option<&CStringArray>,
    ) -> io::Result<zx_handle_t> {
        use crate::sys::process::zircon::*;

        let envp = match maybe_envp {
            // None means to clone the current environment, which is done in the
            // flags below.
            None => ptr::null(),
            Some(envp) => envp.as_ptr(),
        };

        let make_action = |local_io: &ChildStdio, target_fd| -> io::Result<fdio_spawn_action_t> {
            if let Some(local_fd) = local_io.fd() {
                Ok(fdio_spawn_action_t {
                    action: FDIO_SPAWN_ACTION_TRANSFER_FD,
                    local_fd,
                    target_fd,
                    ..Default::default()
                })
            } else {
                if let ChildStdio::Null = local_io {
                    // acts as no-op
                    return Ok(Default::default());
                }

                let mut handle = ZX_HANDLE_INVALID;
                let status = fdio_fd_clone(target_fd, &mut handle);
                if status == ERR_INVALID_ARGS || status == ERR_NOT_SUPPORTED {
                    // This descriptor is closed; skip it rather than generating an
                    // error.
                    return Ok(Default::default());
                }
                zx_cvt(status)?;

                let mut cloned_fd = 0;
                zx_cvt(fdio_fd_create(handle, &mut cloned_fd))?;

                Ok(fdio_spawn_action_t {
                    action: FDIO_SPAWN_ACTION_TRANSFER_FD,
                    local_fd: cloned_fd as i32,
                    target_fd,
                    ..Default::default()
                })
            }
        };

        // Clone stdin, stdout, and stderr
        let action1 = make_action(&stdio.stdin, 0)?;
        let action2 = make_action(&stdio.stdout, 1)?;
        let action3 = make_action(&stdio.stderr, 2)?;
        let actions = [action1, action2, action3];

        // We don't want FileDesc::drop to be called on any stdio. fdio_spawn_etc
        // always consumes transferred file descriptors.
        mem::forget(stdio);

        for callback in self.get_closures().iter_mut() {
            callback()?;
        }

        let mut process_handle: zx_handle_t = 0;
        zx_cvt(fdio_spawn_etc(
            ZX_HANDLE_INVALID,
            FDIO_SPAWN_CLONE_JOB
                | FDIO_SPAWN_CLONE_LDSVC
                | FDIO_SPAWN_CLONE_NAMESPACE
                | FDIO_SPAWN_CLONE_ENVIRON, // this is ignored when envp is non-null
            self.get_program().as_ptr(),
            self.get_argv().as_ptr(),
            envp,
            actions.len() as size_t,
            actions.as_ptr(),
            &mut process_handle,
            ptr::null_mut(),
        ))?;
        // FIXME: See if we want to do something with that err_msg

        Ok(process_handle)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Processes
////////////////////////////////////////////////////////////////////////////////

pub struct Process {
    handle: Handle,
}

impl Process {
    pub fn id(&self) -> u32 {
        self.handle.raw() as u32
    }

    pub fn kill(&mut self) -> io::Result<()> {
        use crate::sys::process::zircon::*;

        unsafe {
            zx_cvt(zx_task_kill(self.handle.raw()))?;
        }

        Ok(())
    }

    pub fn wait(&mut self) -> io::Result<ExitStatus> {
        use crate::default::Default;
        use crate::sys::process::zircon::*;

        let mut proc_info: zx_info_process_t = Default::default();
        let mut actual: size_t = 0;
        let mut avail: size_t = 0;

        unsafe {
            zx_cvt(zx_object_wait_one(
                self.handle.raw(),
                ZX_TASK_TERMINATED,
                ZX_TIME_INFINITE,
                ptr::null_mut(),
            ))?;
            zx_cvt(zx_object_get_info(
                self.handle.raw(),
                ZX_INFO_PROCESS,
                &mut proc_info as *mut _ as *mut libc::c_void,
                mem::size_of::<zx_info_process_t>(),
                &mut actual,
                &mut avail,
            ))?;
        }
        if actual != 1 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Failed to get exit status of process",
            ));
        }
        Ok(ExitStatus(proc_info.return_code))
    }

    pub fn try_wait(&mut self) -> io::Result<Option<ExitStatus>> {
        use crate::default::Default;
        use crate::sys::process::zircon::*;

        let mut proc_info: zx_info_process_t = Default::default();
        let mut actual: size_t = 0;
        let mut avail: size_t = 0;

        unsafe {
            let status =
                zx_object_wait_one(self.handle.raw(), ZX_TASK_TERMINATED, 0, ptr::null_mut());
            match status {
                0 => {} // Success
                x if x == ERR_TIMED_OUT => {
                    return Ok(None);
                }
                _ => {
                    panic!("Failed to wait on process handle: {}", status);
                }
            }
            zx_cvt(zx_object_get_info(
                self.handle.raw(),
                ZX_INFO_PROCESS,
                &mut proc_info as *mut _ as *mut libc::c_void,
                mem::size_of::<zx_info_process_t>(),
                &mut actual,
                &mut avail,
            ))?;
        }
        if actual != 1 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Failed to get exit status of process",
            ));
        }
        Ok(Some(ExitStatus(proc_info.return_code)))
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct ExitStatus(i64);

impl ExitStatus {
    pub fn success(&self) -> bool {
        self.code() == Some(0)
    }

    pub fn code(&self) -> Option<i32> {
        // FIXME: support extracting return code as an i64
        self.0.try_into().ok()
    }

    pub fn signal(&self) -> Option<i32> {
        None
    }
}

impl From<c_int> for ExitStatus {
    fn from(a: c_int) -> ExitStatus {
        ExitStatus(a as i64)
    }
}

impl fmt::Display for ExitStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "exit code: {}", self.0)
    }
}
