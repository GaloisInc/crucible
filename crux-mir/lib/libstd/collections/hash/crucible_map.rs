use crate::borrow::Borrow;
use crate::collections::TryReserveError;
use crate::hash::Hash;
use crate::marker::PhantomData;
use crate::mem;
use crate::slice;
use crate::vec;

/// A simple Vec-based key/value map.  Presents the same API as `hashbrown::HashMap`, so it can be
/// subbed in for `base::HashMap` in the implementation of `std::collections::HashMap`.
#[derive(Clone)]
pub struct HashMap<K, V, S> {
    items: Vec<(K, V)>,
    hasher: S,
    _marker: PhantomData<S>,
}

impl<K, V, S> HashMap<K, V, S> {
    pub fn with_hasher(hash_builder: S) -> HashMap<K, V, S> {
        Self::with_capacity_and_hasher(0, hash_builder)
    }

    pub fn with_capacity_and_hasher(cap: usize, hash_builder: S) -> HashMap<K, V, S> {
        HashMap {
            items: Vec::with_capacity(cap),
            hasher: hash_builder,
            _marker: PhantomData,
        }
    }

    pub fn capacity(&self) -> usize {
        self.items.capacity()
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter { it: self.items.iter() }
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut { it: self.items.iter_mut() }
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn drain(&mut self) -> Drain<'_, K, V> {
        Drain { it: self.items.drain(..) }
    }

    pub fn clear(&mut self) {
        self.items.clear();
    }

    pub fn hasher(&self) -> &S {
        &self.hasher
    }
}

impl<K: Eq + Hash, V, S> HashMap<K, V, S> {
    pub fn reserve(&mut self, additional: usize) {
        self.items.reserve(additional)
    }

    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.items.try_reserve(additional)
    }

    pub fn shrink_to_fit(&mut self) {
        self.items.shrink_to_fit();
    }

    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.items.shrink_to(min_capacity);
    }

    pub fn rustc_entry(&mut self, k: K) -> RustcEntry<'_, K, V> {
        match self.items.iter().position(|&(ref k2, _)| k2 == &k) {
            Some(idx) => RustcEntry::Occupied(RustcOccupiedEntry {
                items: &mut self.items,
                idx,
                k: Some(k),
            }),
            None => RustcEntry::Vacant(RustcVacantEntry {
                items: &mut self.items,
                k,
            }),
        }
    }

    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.get_key_value(k).map(|(_, v)| v)
    }

    pub fn get_key_value<Q: ?Sized>(&self, k: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.items.iter()
            .find(|&(ref k2, _)| k2.borrow() == k)
            .map(|&(ref k, ref v)| (k, v))
    }

    pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.get_key_value(k).is_some()
    }

    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.items.iter_mut()
            .find(|&(ref k2, _)| k2.borrow() == k)
            .map(|&mut (_, ref mut v)| v)
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        match self.rustc_entry(k) {
            RustcEntry::Occupied(mut e) => { Some(e.insert(v)) },
            RustcEntry::Vacant(e) => {
                e.insert(v);
                None
            },
        }
    }

    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.remove_entry(k).map(|(_, v)| v)
    }

    pub fn remove_entry<Q: ?Sized>(&mut self, k: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let idx = self.items.iter().position(|&(ref k2, _)| k2.borrow() == k)?;
        Some(self.items.swap_remove(idx))
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        for i in (0 .. self.items.len()).rev() {
            let (ref k, ref mut v) = self.items[i];
            if !f(k, v) {
                self.items.swap_remove(i);
            }
        }
    }
}


pub struct Iter<'a, K: 'a, V: 'a> {
    it: slice::Iter<'a, (K, V)>,
}

impl<'a, K, V> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Self {
        Iter { it: self.it.clone() }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        let &(ref k, ref v) = self.it.next()?;
        Some((k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.it.size_hint()
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {
    fn len(&self) -> usize {
        self.it.len()
    }
}


pub struct IterMut<'a, K: 'a, V: 'a> {
    it: slice::IterMut<'a, (K, V)>,
}

impl<'a, K, V> IterMut<'a, K, V> {
    pub fn rustc_iter(&self) -> Iter<'_, K, V> {
        Iter {
            it: self.it.as_slice().iter(),
        }
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        let &mut (ref k, ref mut v) = self.it.next()?;
        Some((k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.it.size_hint()
    }
}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {
    fn len(&self) -> usize {
        self.it.len()
    }
}


impl<K, V, S> IntoIterator for HashMap<K, V, S> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    #[inline]
    fn into_iter(self) -> IntoIter<K, V> {
        IntoIter {
            it: self.items.into_iter(),
        }
    }
}

pub struct IntoIter<K, V> {
    it: vec::IntoIter<(K, V)>,
}

impl<K, V> IntoIter<K, V> {
    pub fn rustc_iter(&self) -> Iter<'_, K, V> {
        Iter {
            it: self.it.as_slice().iter(),
        }
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        self.it.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.it.size_hint()
    }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    fn len(&self) -> usize {
        self.it.len()
    }
}


pub struct Drain<'a, K, V> {
    it: vec::Drain<'a, (K, V)>,
}

impl<'a, K, V> Drain<'a, K, V> {
    pub fn rustc_iter(&self) -> Iter<'_, K, V> {
        Iter {
            it: self.it.as_slice().iter(),
        }
    }
}

impl<'a, K, V> Iterator for Drain<'a, K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        self.it.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.it.size_hint()
    }
}

impl<'a, K, V> ExactSizeIterator for Drain<'a, K, V> {
    fn len(&self) -> usize {
        self.it.len()
    }
}


impl<K, V, S> Extend<(K, V)> for HashMap<K, V, S>
where
    K: Eq + Hash,
{
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<'a, K, V, S> Extend<(&'a K, &'a V)> for HashMap<K, V, S>
where
    K: Eq + Hash + Copy,
    V: Copy,
{
    #[inline]
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
        self.extend(iter.into_iter().map(|(&key, &value)| (key, value)));
    }
}


pub enum RustcEntry<'a, K: 'a, V: 'a> {
    Occupied(RustcOccupiedEntry<'a, K, V>),
    Vacant(RustcVacantEntry<'a, K, V>),
}

pub struct RustcOccupiedEntry<'a, K, V> {
    items: &'a mut Vec<(K, V)>,
    idx: usize,
    k: Option<K>,
}

pub struct RustcVacantEntry<'a, K, V> {
    items: &'a mut Vec<(K, V)>,
    k: K,
}

impl<'a, K, V> RustcOccupiedEntry<'a, K, V> {
    pub fn key(&self) -> &K {
        &self.items[self.idx].0
    }

    pub fn remove_entry(self) -> (K, V) {
        self.items.swap_remove(self.idx)
    }

    pub fn get(&self) -> &V {
        &self.items[self.idx].1
    }

    pub fn get_mut(&mut self) -> &mut V {
        &mut self.items[self.idx].1
    }

    pub fn into_mut(self) -> &'a mut V {
        &mut self.items[self.idx].1
    }

    pub fn insert(&mut self, v: V) -> V {
        mem::replace(self.get_mut(), v)
    }

    pub fn remove(self) -> V {
        self.remove_entry().1
    }

    pub fn replace_entry(self, v: V) -> (K, V) {
        mem::replace(&mut self.items[self.idx], (self.k.unwrap(), v))
    }

    pub fn replace_key(self) -> K {
        mem::replace(&mut self.items[self.idx].0, self.k.unwrap())
    }
}

impl<'a, K, V> RustcVacantEntry<'a, K, V> {
    pub fn key(&self) -> &K {
        &self.k
    }

    pub fn into_key(self) -> K {
        self.k
    }

    pub fn insert(self, v: V) -> &'a mut V {
        self.items.push((self.k, v));
        &mut self.items.last_mut().unwrap().1
    }

    pub fn insert_entry(self, v: V) -> RustcOccupiedEntry<'a, K, V> {
        let idx = self.items.len();
        self.items.push((self.k, v));
        RustcOccupiedEntry {
            items: self.items,
            idx,
            k: None,
        }
    }
}
