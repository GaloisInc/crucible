//! Helper module which helps to determine amount of threads to be used
//! during tests execution.
use std::env;

#[allow(deprecated)]
pub fn get_concurrency() -> usize {
    return match env::var("RUST_TEST_THREADS") {
        Ok(s) => {
            let opt_n: Option<usize> = s.parse().ok();
            match opt_n {
                Some(n) if n > 0 => n,
                _ => panic!("RUST_TEST_THREADS is `{}`, should be a positive integer.", s),
            }
        }
        Err(..) => num_cpus(),
    };

    #[cfg(windows)]
    #[allow(nonstandard_style)]
    fn num_cpus() -> usize {
        #[repr(C)]
        struct SYSTEM_INFO {
            wProcessorArchitecture: u16,
            wReserved: u16,
            dwPageSize: u32,
            lpMinimumApplicationAddress: *mut u8,
            lpMaximumApplicationAddress: *mut u8,
            dwActiveProcessorMask: *mut u8,
            dwNumberOfProcessors: u32,
            dwProcessorType: u32,
            dwAllocationGranularity: u32,
            wProcessorLevel: u16,
            wProcessorRevision: u16,
        }
        extern "system" {
            fn GetSystemInfo(info: *mut SYSTEM_INFO) -> i32;
        }
        unsafe {
            let mut sysinfo = std::mem::zeroed();
            GetSystemInfo(&mut sysinfo);
            sysinfo.dwNumberOfProcessors as usize
        }
    }

    #[cfg(target_os = "vxworks")]
    fn num_cpus() -> usize {
        // FIXME: Implement num_cpus on vxWorks
        1
    }

    #[cfg(target_os = "redox")]
    fn num_cpus() -> usize {
        // FIXME: Implement num_cpus on Redox
        1
    }

    #[cfg(target_os = "hermit")]
    fn num_cpus() -> usize {
        // FIXME: Implement num_cpus on HermitCore
        1
    }

    #[cfg(any(
        all(target_arch = "wasm32", not(target_os = "emscripten")),
        all(target_vendor = "fortanix", target_env = "sgx")
    ))]
    fn num_cpus() -> usize {
        1
    }

    #[cfg(any(
        target_os = "android",
        target_os = "cloudabi",
        target_os = "emscripten",
        target_os = "fuchsia",
        target_os = "ios",
        target_os = "linux",
        target_os = "macos",
        target_os = "solaris",
    ))]
    fn num_cpus() -> usize {
        unsafe { libc::sysconf(libc::_SC_NPROCESSORS_ONLN) as usize }
    }

    #[cfg(any(target_os = "freebsd", target_os = "dragonfly", target_os = "netbsd"))]
    fn num_cpus() -> usize {
        use std::ptr;

        let mut cpus: libc::c_uint = 0;
        let mut cpus_size = std::mem::size_of_val(&cpus);

        unsafe {
            cpus = libc::sysconf(libc::_SC_NPROCESSORS_ONLN) as libc::c_uint;
        }
        if cpus < 1 {
            let mut mib = [libc::CTL_HW, libc::HW_NCPU, 0, 0];
            unsafe {
                libc::sysctl(
                    mib.as_mut_ptr(),
                    2,
                    &mut cpus as *mut _ as *mut _,
                    &mut cpus_size as *mut _ as *mut _,
                    ptr::null_mut(),
                    0,
                );
            }
            if cpus < 1 {
                cpus = 1;
            }
        }
        cpus as usize
    }

    #[cfg(target_os = "openbsd")]
    fn num_cpus() -> usize {
        use std::ptr;

        let mut cpus: libc::c_uint = 0;
        let mut cpus_size = std::mem::size_of_val(&cpus);
        let mut mib = [libc::CTL_HW, libc::HW_NCPU, 0, 0];

        unsafe {
            libc::sysctl(
                mib.as_mut_ptr(),
                2,
                &mut cpus as *mut _ as *mut _,
                &mut cpus_size as *mut _ as *mut _,
                ptr::null_mut(),
                0,
            );
        }
        if cpus < 1 {
            cpus = 1;
        }
        cpus as usize
    }

    #[cfg(target_os = "haiku")]
    fn num_cpus() -> usize {
        // FIXME: implement
        1
    }

    #[cfg(target_os = "l4re")]
    fn num_cpus() -> usize {
        // FIXME: implement
        1
    }
}
