//! Windows-specific extensions to primitives in the [`std::process`] module.
//!
//! [`std::process`]: crate::process

#![stable(feature = "process_extensions", since = "1.2.0")]

use crate::ffi::OsStr;
use crate::os::windows::io::{
    AsHandle, AsRawHandle, BorrowedHandle, FromRawHandle, IntoRawHandle, OwnedHandle, RawHandle,
};
use crate::process;
use crate::sealed::Sealed;
use crate::sys;
use crate::sys_common::{AsInner, AsInnerMut, FromInner, IntoInner};

#[stable(feature = "process_extensions", since = "1.2.0")]
impl FromRawHandle for process::Stdio {
    unsafe fn from_raw_handle(handle: RawHandle) -> process::Stdio {
        let handle = sys::handle::Handle::from_raw_handle(handle as *mut _);
        let io = sys::process::Stdio::Handle(handle);
        process::Stdio::from_inner(io)
    }
}

#[stable(feature = "io_safety", since = "1.63.0")]
impl From<OwnedHandle> for process::Stdio {
    fn from(handle: OwnedHandle) -> process::Stdio {
        let handle = sys::handle::Handle::from_inner(handle);
        let io = sys::process::Stdio::Handle(handle);
        process::Stdio::from_inner(io)
    }
}

#[stable(feature = "process_extensions", since = "1.2.0")]
impl AsRawHandle for process::Child {
    #[inline]
    fn as_raw_handle(&self) -> RawHandle {
        self.as_inner().handle().as_raw_handle() as *mut _
    }
}

#[stable(feature = "io_safety", since = "1.63.0")]
impl AsHandle for process::Child {
    #[inline]
    fn as_handle(&self) -> BorrowedHandle<'_> {
        self.as_inner().handle().as_handle()
    }
}

#[stable(feature = "into_raw_os", since = "1.4.0")]
impl IntoRawHandle for process::Child {
    fn into_raw_handle(self) -> RawHandle {
        self.into_inner().into_handle().into_raw_handle() as *mut _
    }
}

#[stable(feature = "io_safety", since = "1.63.0")]
impl From<process::Child> for OwnedHandle {
    fn from(child: process::Child) -> OwnedHandle {
        child.into_inner().into_handle().into_inner()
    }
}

#[stable(feature = "process_extensions", since = "1.2.0")]
impl AsRawHandle for process::ChildStdin {
    #[inline]
    fn as_raw_handle(&self) -> RawHandle {
        self.as_inner().handle().as_raw_handle() as *mut _
    }
}

#[stable(feature = "process_extensions", since = "1.2.0")]
impl AsRawHandle for process::ChildStdout {
    #[inline]
    fn as_raw_handle(&self) -> RawHandle {
        self.as_inner().handle().as_raw_handle() as *mut _
    }
}

#[stable(feature = "process_extensions", since = "1.2.0")]
impl AsRawHandle for process::ChildStderr {
    #[inline]
    fn as_raw_handle(&self) -> RawHandle {
        self.as_inner().handle().as_raw_handle() as *mut _
    }
}

#[stable(feature = "into_raw_os", since = "1.4.0")]
impl IntoRawHandle for process::ChildStdin {
    fn into_raw_handle(self) -> RawHandle {
        self.into_inner().into_handle().into_raw_handle() as *mut _
    }
}

#[stable(feature = "into_raw_os", since = "1.4.0")]
impl IntoRawHandle for process::ChildStdout {
    fn into_raw_handle(self) -> RawHandle {
        self.into_inner().into_handle().into_raw_handle() as *mut _
    }
}

#[stable(feature = "into_raw_os", since = "1.4.0")]
impl IntoRawHandle for process::ChildStderr {
    fn into_raw_handle(self) -> RawHandle {
        self.into_inner().into_handle().into_raw_handle() as *mut _
    }
}

/// Windows-specific extensions to [`process::ExitStatus`].
///
/// This trait is sealed: it cannot be implemented outside the standard library.
/// This is so that future additional methods are not breaking changes.
#[stable(feature = "exit_status_from", since = "1.12.0")]
pub trait ExitStatusExt: Sealed {
    /// Creates a new `ExitStatus` from the raw underlying `u32` return value of
    /// a process.
    #[stable(feature = "exit_status_from", since = "1.12.0")]
    fn from_raw(raw: u32) -> Self;
}

#[stable(feature = "exit_status_from", since = "1.12.0")]
impl ExitStatusExt for process::ExitStatus {
    fn from_raw(raw: u32) -> Self {
        process::ExitStatus::from_inner(From::from(raw))
    }
}

/// Windows-specific extensions to the [`process::Command`] builder.
///
/// This trait is sealed: it cannot be implemented outside the standard library.
/// This is so that future additional methods are not breaking changes.
#[stable(feature = "windows_process_extensions", since = "1.16.0")]
pub trait CommandExt: Sealed {
    /// Sets the [process creation flags][1] to be passed to `CreateProcess`.
    ///
    /// These will always be ORed with `CREATE_UNICODE_ENVIRONMENT`.
    ///
    /// [1]: https://docs.microsoft.com/en-us/windows/win32/procthread/process-creation-flags
    #[stable(feature = "windows_process_extensions", since = "1.16.0")]
    fn creation_flags(&mut self, flags: u32) -> &mut process::Command;

    /// Forces all arguments to be wrapped in quote (`"`) characters.
    ///
    /// This is useful for passing arguments to [MSYS2/Cygwin][1] based
    /// executables: these programs will expand unquoted arguments containing
    /// wildcard characters (`?` and `*`) by searching for any file paths
    /// matching the wildcard pattern.
    ///
    /// Adding quotes has no effect when passing arguments to programs
    /// that use [msvcrt][2]. This includes programs built with both
    /// MinGW and MSVC.
    ///
    /// [1]: <https://github.com/msys2/MSYS2-packages/issues/2176>
    /// [2]: <https://msdn.microsoft.com/en-us/library/17w5ykft.aspx>
    #[unstable(feature = "windows_process_extensions_force_quotes", issue = "82227")]
    fn force_quotes(&mut self, enabled: bool) -> &mut process::Command;

    /// Append literal text to the command line without any quoting or escaping.
    ///
    /// This is useful for passing arguments to `cmd.exe /c`, which doesn't follow
    /// `CommandLineToArgvW` escaping rules.
    #[stable(feature = "windows_process_extensions_raw_arg", since = "1.62.0")]
    fn raw_arg<S: AsRef<OsStr>>(&mut self, text_to_append_as_is: S) -> &mut process::Command;

    /// When [`process::Command`] creates pipes, request that our side is always async.
    ///
    /// By default [`process::Command`] may choose to use pipes where both ends
    /// are opened for synchronous read or write operations. By using
    /// `async_pipes(true)`, this behavior is overridden so that our side is
    /// always async.
    ///
    /// This is important because if doing async I/O a pipe or a file has to be
    /// opened for async access.
    ///
    /// The end of the pipe sent to the child process will always be synchronous
    /// regardless of this option.
    ///
    /// # Example
    ///
    /// ```
    /// #![feature(windows_process_extensions_async_pipes)]
    /// use std::os::windows::process::CommandExt;
    /// use std::process::{Command, Stdio};
    ///
    /// # let program = "";
    ///
    /// Command::new(program)
    ///     .async_pipes(true)
    ///     .stdin(Stdio::piped())
    ///     .stdout(Stdio::piped())
    ///     .stderr(Stdio::piped());
    /// ```
    #[unstable(feature = "windows_process_extensions_async_pipes", issue = "98289")]
    fn async_pipes(&mut self, always_async: bool) -> &mut process::Command;
}

#[stable(feature = "windows_process_extensions", since = "1.16.0")]
impl CommandExt for process::Command {
    fn creation_flags(&mut self, flags: u32) -> &mut process::Command {
        self.as_inner_mut().creation_flags(flags);
        self
    }

    fn force_quotes(&mut self, enabled: bool) -> &mut process::Command {
        self.as_inner_mut().force_quotes(enabled);
        self
    }

    fn raw_arg<S: AsRef<OsStr>>(&mut self, raw_text: S) -> &mut process::Command {
        self.as_inner_mut().raw_arg(raw_text.as_ref());
        self
    }

    fn async_pipes(&mut self, always_async: bool) -> &mut process::Command {
        // FIXME: This currently has an intentional no-op implementation.
        // For the time being our side of the pipes will always be async.
        // Once the ecosystem has adjusted, we may then be able to start making
        // use of synchronous pipes within the standard library.
        let _ = always_async;
        self
    }
}

#[unstable(feature = "windows_process_extensions_main_thread_handle", issue = "96723")]
pub trait ChildExt: Sealed {
    /// Extracts the main thread raw handle, without taking ownership
    #[unstable(feature = "windows_process_extensions_main_thread_handle", issue = "96723")]
    fn main_thread_handle(&self) -> BorrowedHandle<'_>;
}

#[unstable(feature = "windows_process_extensions_main_thread_handle", issue = "96723")]
impl ChildExt for process::Child {
    fn main_thread_handle(&self) -> BorrowedHandle<'_> {
        self.handle.main_thread_handle()
    }
}

/// Windows-specific extensions to [`process::ExitCode`].
///
/// This trait is sealed: it cannot be implemented outside the standard library.
/// This is so that future additional methods are not breaking changes.
#[unstable(feature = "windows_process_exit_code_from", issue = "none")]
pub trait ExitCodeExt: Sealed {
    /// Creates a new `ExitCode` from the raw underlying `u32` return value of
    /// a process.
    ///
    /// The exit code should not be 259, as this conflicts with the `STILL_ACTIVE`
    /// macro returned from the `GetExitCodeProcess` function to signal that the
    /// process has yet to run to completion.
    #[unstable(feature = "windows_process_exit_code_from", issue = "none")]
    fn from_raw(raw: u32) -> Self;
}

#[unstable(feature = "windows_process_exit_code_from", issue = "none")]
impl ExitCodeExt for process::ExitCode {
    fn from_raw(raw: u32) -> Self {
        process::ExitCode::from_inner(From::from(raw))
    }
}
