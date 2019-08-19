use crate::fmt::{self, dummy, dummy_val};
use crate::marker::PhantomData;

#[must_use = "must eventually call `finish()` on Debug builders"]
#[allow(missing_debug_implementations)]
#[stable(feature = "debug_builders", since = "1.2.0")]
pub struct DebugStruct<'a, 'b: 'a> {
    _marker: PhantomData<&'a mut fmt::Formatter<'b>>,
}

pub fn debug_struct_new<'a, 'b>(fmt: &'a mut fmt::Formatter<'b>,
                                name: &str)
                                -> DebugStruct<'a, 'b> {
    dummy_val(DebugStruct { _marker: PhantomData })
}

impl<'a, 'b: 'a> DebugStruct<'a, 'b> {
    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn field(&mut self, name: &str, value: &dyn fmt::Debug) -> &mut DebugStruct<'a, 'b> {
        dummy_val(self)
    }

    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn finish(&mut self) -> fmt::Result {
        dummy()
    }
}

#[must_use = "must eventually call `finish()` on Debug builders"]
#[allow(missing_debug_implementations)]
#[stable(feature = "debug_builders", since = "1.2.0")]
pub struct DebugTuple<'a, 'b: 'a> {
    _marker: PhantomData<&'a mut fmt::Formatter<'b>>,
}

pub fn debug_tuple_new<'a, 'b>(fmt: &'a mut fmt::Formatter<'b>, name: &str) -> DebugTuple<'a, 'b> {
    dummy_val(DebugTuple { _marker: PhantomData })
}

impl<'a, 'b: 'a> DebugTuple<'a, 'b> {
    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn field(&mut self, value: &dyn fmt::Debug) -> &mut DebugTuple<'a, 'b> {
        dummy_val(self)
    }

    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn finish(&mut self) -> fmt::Result {
        dummy()
    }
}

#[must_use = "must eventually call `finish()` on Debug builders"]
#[allow(missing_debug_implementations)]
#[stable(feature = "debug_builders", since = "1.2.0")]
pub struct DebugSet<'a, 'b: 'a> {
    _marker: PhantomData<&'a mut fmt::Formatter<'b>>,
}

pub fn debug_set_new<'a, 'b>(fmt: &'a mut fmt::Formatter<'b>) -> DebugSet<'a, 'b> {
    dummy_val(DebugSet { _marker: PhantomData })
}

impl<'a, 'b: 'a> DebugSet<'a, 'b> {
    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn entry(&mut self, entry: &dyn fmt::Debug) -> &mut DebugSet<'a, 'b> {
        dummy_val(self)
    }

    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn entries<D, I>(&mut self, entries: I) -> &mut DebugSet<'a, 'b>
        where D: fmt::Debug,
              I: IntoIterator<Item = D>
    {
        dummy_val(self)
    }

    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn finish(&mut self) -> fmt::Result {
        dummy()
    }
}

#[must_use = "must eventually call `finish()` on Debug builders"]
#[allow(missing_debug_implementations)]
#[stable(feature = "debug_builders", since = "1.2.0")]
pub struct DebugList<'a, 'b: 'a> {
    _marker: PhantomData<&'a mut fmt::Formatter<'b>>,
}

pub fn debug_list_new<'a, 'b>(fmt: &'a mut fmt::Formatter<'b>) -> DebugList<'a, 'b> {
    dummy_val(DebugList { _marker: PhantomData })
}

impl<'a, 'b: 'a> DebugList<'a, 'b> {
    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn entry(&mut self, entry: &dyn fmt::Debug) -> &mut DebugList<'a, 'b> {
        dummy_val(self)
    }

    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn entries<D, I>(&mut self, entries: I) -> &mut DebugList<'a, 'b>
        where D: fmt::Debug,
              I: IntoIterator<Item = D>
    {
        dummy_val(self)
    }

    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn finish(&mut self) -> fmt::Result {
        dummy()
    }
}

#[must_use = "must eventually call `finish()` on Debug builders"]
#[allow(missing_debug_implementations)]
#[stable(feature = "debug_builders", since = "1.2.0")]
pub struct DebugMap<'a, 'b: 'a> {
    _marker: PhantomData<&'a mut fmt::Formatter<'b>>,
}

pub fn debug_map_new<'a, 'b>(fmt: &'a mut fmt::Formatter<'b>) -> DebugMap<'a, 'b> {
    dummy_val(DebugMap { _marker: PhantomData })
}

impl<'a, 'b: 'a> DebugMap<'a, 'b> {
    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn entry(&mut self, key: &dyn fmt::Debug, value: &dyn fmt::Debug) -> &mut DebugMap<'a, 'b> {
        dummy_val(self)
    }

    #[unstable(feature = "debug_map_key_value",
               reason = "recently added",
               issue = "62482")]
    pub fn key(&mut self, key: &dyn fmt::Debug) -> &mut DebugMap<'a, 'b> {
        dummy_val(self)
    }

    #[unstable(feature = "debug_map_key_value",
               reason = "recently added",
               issue = "62482")]
    pub fn value(&mut self, value: &dyn fmt::Debug) -> &mut DebugMap<'a, 'b> {
        dummy_val(self)
    }

    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn entries<K, V, I>(&mut self, entries: I) -> &mut DebugMap<'a, 'b>
        where K: fmt::Debug,
              V: fmt::Debug,
              I: IntoIterator<Item = (K, V)>
    {
        dummy_val(self)
    }

    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn finish(&mut self) -> fmt::Result {
        dummy()
    }
}
