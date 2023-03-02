use core::convert::TryInto;
use core::time::Duration;
use crate::sys;
use crate::sys_common::FromInner;


#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Instant(u64);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct SystemTime(i64);

pub const UNIX_EPOCH: SystemTime = SystemTime(0);

impl Instant {
    pub fn now() -> Instant {
        Instant(0)
    }

    pub const fn zero() -> Instant {
        Instant(0)
    }

    pub fn actually_monotonic() -> bool {
        true
    }

    pub fn checked_sub_instant(&self, other: &Instant) -> Option<Duration> {
        Some(Duration::from_nanos(self.0.checked_sub(other.0)?))
    }

    pub fn checked_add_duration(&self, other: &Duration) -> Option<Instant> {
        Some(Instant(self.0.checked_add(other.as_nanos().try_into().ok()?)?))
    }

    pub fn checked_sub_duration(&self, other: &Duration) -> Option<Instant> {
        Some(Instant(self.0.checked_sub(other.as_nanos().try_into().ok()?)?))
    }
}

impl SystemTime {
    pub fn now() -> SystemTime {
        SystemTime(0)
    }

    pub fn sub_time(&self, other: &SystemTime) -> Result<Duration, Duration> {
        if self.0 >= other.0 {
            Ok(Duration::from_nanos((self.0 - other.0) as u64))
        } else {
            Err(Duration::from_nanos((other.0 - self.0) as u64))
        }
    }

    pub fn checked_add_duration(&self, other: &Duration) -> Option<SystemTime> {
        Some(SystemTime(self.0.checked_add(other.as_nanos().try_into().ok()?)?))
    }

    pub fn checked_sub_duration(&self, other: &Duration) -> Option<SystemTime> {
        Some(SystemTime(self.0.checked_sub(other.as_nanos().try_into().ok()?)?))
    }
}

impl FromInner<sys::time::SystemTime> for SystemTime {
    fn from_inner(time: sys::time::SystemTime) -> SystemTime {
        match time.sub_time(&sys::time::UNIX_EPOCH) {
            Ok(pos) => UNIX_EPOCH.checked_add_duration(&pos).unwrap(),
            Err(neg) => UNIX_EPOCH.checked_sub_duration(&neg).unwrap(),
        }
    }
}
