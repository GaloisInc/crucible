#![allow(dead_code)]

use crate::cmp::Ordering;
use crate::convert::TryInto;
use crate::sys::hermit::abi;
use crate::sys::hermit::abi::timespec;
use crate::sys::hermit::abi::{CLOCK_MONOTONIC, CLOCK_REALTIME, NSEC_PER_SEC};
use crate::time::Duration;
use core::hash::{Hash, Hasher};

#[derive(Copy, Clone, Debug)]
struct Timespec {
    t: timespec,
}

impl Timespec {
    const fn zero() -> Timespec {
        Timespec { t: timespec { tv_sec: 0, tv_nsec: 0 } }
    }

    fn sub_timespec(&self, other: &Timespec) -> Result<Duration, Duration> {
        if self >= other {
            Ok(if self.t.tv_nsec >= other.t.tv_nsec {
                Duration::new(
                    (self.t.tv_sec - other.t.tv_sec) as u64,
                    (self.t.tv_nsec - other.t.tv_nsec) as u32,
                )
            } else {
                Duration::new(
                    (self.t.tv_sec - 1 - other.t.tv_sec) as u64,
                    self.t.tv_nsec as u32 + (NSEC_PER_SEC as u32) - other.t.tv_nsec as u32,
                )
            })
        } else {
            match other.sub_timespec(self) {
                Ok(d) => Err(d),
                Err(d) => Ok(d),
            }
        }
    }

    fn checked_add_duration(&self, other: &Duration) -> Option<Timespec> {
        let mut secs = other
            .as_secs()
            .try_into() // <- target type would be `libc::time_t`
            .ok()
            .and_then(|secs| self.t.tv_sec.checked_add(secs))?;

        // Nano calculations can't overflow because nanos are <1B which fit
        // in a u32.
        let mut nsec = other.subsec_nanos() + self.t.tv_nsec as u32;
        if nsec >= NSEC_PER_SEC as u32 {
            nsec -= NSEC_PER_SEC as u32;
            secs = secs.checked_add(1)?;
        }
        Some(Timespec { t: timespec { tv_sec: secs, tv_nsec: nsec as _ } })
    }

    fn checked_sub_duration(&self, other: &Duration) -> Option<Timespec> {
        let mut secs = other
            .as_secs()
            .try_into() // <- target type would be `libc::time_t`
            .ok()
            .and_then(|secs| self.t.tv_sec.checked_sub(secs))?;

        // Similar to above, nanos can't overflow.
        let mut nsec = self.t.tv_nsec as i32 - other.subsec_nanos() as i32;
        if nsec < 0 {
            nsec += NSEC_PER_SEC as i32;
            secs = secs.checked_sub(1)?;
        }
        Some(Timespec { t: timespec { tv_sec: secs, tv_nsec: nsec as _ } })
    }
}

impl PartialEq for Timespec {
    fn eq(&self, other: &Timespec) -> bool {
        self.t.tv_sec == other.t.tv_sec && self.t.tv_nsec == other.t.tv_nsec
    }
}

impl Eq for Timespec {}

impl PartialOrd for Timespec {
    fn partial_cmp(&self, other: &Timespec) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Timespec {
    fn cmp(&self, other: &Timespec) -> Ordering {
        let me = (self.t.tv_sec, self.t.tv_nsec);
        let other = (other.t.tv_sec, other.t.tv_nsec);
        me.cmp(&other)
    }
}

impl Hash for Timespec {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.t.tv_sec.hash(state);
        self.t.tv_nsec.hash(state);
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Instant {
    t: Timespec,
}

impl Instant {
    pub fn now() -> Instant {
        let mut time: Timespec = Timespec::zero();
        let _ = unsafe { abi::clock_gettime(CLOCK_MONOTONIC, &mut time.t as *mut timespec) };

        Instant { t: time }
    }

    pub const fn zero() -> Instant {
        Instant { t: Timespec::zero() }
    }

    pub fn actually_monotonic() -> bool {
        true
    }

    pub fn checked_sub_instant(&self, other: &Instant) -> Option<Duration> {
        self.t.sub_timespec(&other.t).ok()
    }

    pub fn checked_add_duration(&self, other: &Duration) -> Option<Instant> {
        Some(Instant { t: self.t.checked_add_duration(other)? })
    }

    pub fn checked_sub_duration(&self, other: &Duration) -> Option<Instant> {
        Some(Instant { t: self.t.checked_sub_duration(other)? })
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct SystemTime {
    t: Timespec,
}

pub const UNIX_EPOCH: SystemTime = SystemTime { t: Timespec::zero() };

impl SystemTime {
    pub fn now() -> SystemTime {
        let mut time: Timespec = Timespec::zero();
        let _ = unsafe { abi::clock_gettime(CLOCK_REALTIME, &mut time.t as *mut timespec) };

        SystemTime { t: time }
    }

    pub fn sub_time(&self, other: &SystemTime) -> Result<Duration, Duration> {
        self.t.sub_timespec(&other.t)
    }

    pub fn checked_add_duration(&self, other: &Duration) -> Option<SystemTime> {
        Some(SystemTime { t: self.t.checked_add_duration(other)? })
    }

    pub fn checked_sub_duration(&self, other: &Duration) -> Option<SystemTime> {
        Some(SystemTime { t: self.t.checked_sub_duration(other)? })
    }
}
