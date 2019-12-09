use crate::mem;
use crate::slice;

pub fn hashmap_random_keys() -> (u64, u64) {
    let mut v = (0, 0);
    unsafe {
        let view = slice::from_raw_parts_mut(&mut v as *mut _ as *mut u8,
                                             mem::size_of_val(&v));
        imp::fill_bytes(view);
    }
    return v
}

#[cfg(all(unix,
          not(target_os = "ios"),
          not(target_os = "openbsd"),
          not(target_os = "freebsd"),
          not(target_os = "fuchsia")))]
mod imp {
    use crate::fs::File;
    use crate::io::Read;

    #[cfg(any(target_os = "linux", target_os = "android"))]
    fn getrandom(buf: &mut [u8]) -> libc::c_long {
        unsafe {
            libc::syscall(libc::SYS_getrandom, buf.as_mut_ptr(), buf.len(), libc::GRND_NONBLOCK)
        }
    }

    #[cfg(not(any(target_os = "linux", target_os = "android")))]
    fn getrandom_fill_bytes(_buf: &mut [u8]) -> bool { false }

    #[cfg(any(target_os = "linux", target_os = "android"))]
    fn getrandom_fill_bytes(v: &mut [u8]) -> bool {
        use crate::sync::atomic::{AtomicBool, Ordering};
        use crate::sys::os::errno;

        static GETRANDOM_UNAVAILABLE: AtomicBool = AtomicBool::new(false);
        if GETRANDOM_UNAVAILABLE.load(Ordering::Relaxed) {
            return false;
        }

        let mut read = 0;
        while read < v.len() {
            let result = getrandom(&mut v[read..]);
            if result == -1 {
                let err = errno() as libc::c_int;
                if err == libc::EINTR {
                    continue;
                } else if err == libc::ENOSYS || err == libc::EPERM {
                    // Fall back to reading /dev/urandom if `getrandom` is not
                    // supported on the current kernel.
                    //
                    // Also fall back in case it is disabled by something like
                    // seccomp or inside of virtual machines.
                    GETRANDOM_UNAVAILABLE.store(true, Ordering::Relaxed);
                    return false;
                } else if err == libc::EAGAIN {
                    return false;
                } else {
                    panic!("unexpected getrandom error: {}", err);
                }
            } else {
                read += result as usize;
            }
        }
        true
    }

    pub fn fill_bytes(v: &mut [u8]) {
        // getrandom_fill_bytes here can fail if getrandom() returns EAGAIN,
        // meaning it would have blocked because the non-blocking pool (urandom)
        // has not initialized in the kernel yet due to a lack of entropy. The
        // fallback we do here is to avoid blocking applications which could
        // depend on this call without ever knowing they do and don't have a
        // work around. The PRNG of /dev/urandom will still be used but over a
        // possibly predictable entropy pool.
        if getrandom_fill_bytes(v) {
            return;
        }

        // getrandom failed because it is permanently or temporarily (because
        // of missing entropy) unavailable. Open /dev/urandom, read from it,
        // and close it again.
        let mut file = File::open("/dev/urandom").expect("failed to open /dev/urandom");
        file.read_exact(v).expect("failed to read /dev/urandom")
    }
}

#[cfg(target_os = "openbsd")]
mod imp {
    use crate::sys::os::errno;

    pub fn fill_bytes(v: &mut [u8]) {
        // getentropy(2) permits a maximum buffer size of 256 bytes
        for s in v.chunks_mut(256) {
            let ret = unsafe {
                libc::getentropy(s.as_mut_ptr() as *mut libc::c_void, s.len())
            };
            if ret == -1 {
                panic!("unexpected getentropy error: {}", errno());
            }
        }
    }
}

// On iOS and MacOS `SecRandomCopyBytes` calls `CCRandomCopyBytes` with
// `kCCRandomDefault`. `CCRandomCopyBytes` manages a CSPRNG which is seeded
// from `/dev/random` and which runs on its own thread accessed via GCD.
// This seems needlessly heavyweight for the purposes of generating two u64s
// once per thread in `hashmap_random_keys`. Therefore `SecRandomCopyBytes` is
// only used on iOS where direct access to `/dev/urandom` is blocked by the
// sandbox.
#[cfg(target_os = "ios")]
mod imp {
    use crate::io;
    use crate::ptr;
    use libc::{c_int, size_t};

    enum SecRandom {}

    #[allow(non_upper_case_globals)]
    const kSecRandomDefault: *const SecRandom = ptr::null();

    extern {
        fn SecRandomCopyBytes(rnd: *const SecRandom,
                              count: size_t,
                              bytes: *mut u8) -> c_int;
    }

    pub fn fill_bytes(v: &mut [u8]) {
        let ret = unsafe {
            SecRandomCopyBytes(kSecRandomDefault,
                               v.len(),
                               v.as_mut_ptr())
        };
        if ret == -1 {
            panic!("couldn't generate random bytes: {}",
                   io::Error::last_os_error());
        }
    }
}

#[cfg(target_os = "freebsd")]
mod imp {
    use crate::ptr;

    pub fn fill_bytes(v: &mut [u8]) {
        let mib = [libc::CTL_KERN, libc::KERN_ARND];
        // kern.arandom permits a maximum buffer size of 256 bytes
        for s in v.chunks_mut(256) {
            let mut s_len = s.len();
            let ret = unsafe {
                libc::sysctl(mib.as_ptr(), mib.len() as libc::c_uint,
                             s.as_mut_ptr() as *mut _, &mut s_len,
                             ptr::null(), 0)
            };
            if ret == -1 || s_len != s.len() {
                panic!("kern.arandom sysctl failed! (returned {}, s.len() {}, oldlenp {})",
                       ret, s.len(), s_len);
            }
        }
    }
}

#[cfg(target_os = "fuchsia")]
mod imp {
    #[link(name = "zircon")]
    extern {
        fn zx_cprng_draw(buffer: *mut u8, len: usize);
    }

    pub fn fill_bytes(v: &mut [u8]) {
        unsafe { zx_cprng_draw(v.as_mut_ptr(), v.len()) }
    }
}
