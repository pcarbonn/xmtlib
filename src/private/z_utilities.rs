// Copyright Pierre Carbonnelle, 2025.

use std::fmt::Display;
use std::hash::Hash;

use indexmap::{IndexMap, map::Iter};

use crate::error::Offset;

/// An IndexMap that maps keys to optional values.  Values are not erased by an insert.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OptionMap<K: Hash + Eq + Clone, V: Clone>(IndexMap<K, Option<V>>);

impl<K: Hash + Eq + Clone, V: Clone> OptionMap<K, V> {

    pub(crate) fn new() -> Self {
        OptionMap(IndexMap::new())
    }

    pub(crate) fn insert(&mut self, key: K, value: Option<V>) -> () {
        match self.0.get(&key) {
            None          => { self.0.insert(key, value); },
            Some(None)    => { self.0.insert(key, value); },
            Some(Some(_)) => {}
            }
    }

    pub(crate) fn append(&mut self, other: &mut OptionMap<K, V>) {
        for (key, value) in other.iter() {
            self.insert(key.clone(), value.clone());
        }
    }
    pub(crate) fn shift_remove(&mut self, key: &K) -> Option<Option<V>> {
        self.0.shift_remove(key)
    }

    pub(crate) fn get(&self, key: &K) -> Option<&Option<V>> {
        self.0.get(key)
    }

    pub fn iter(&self) -> Iter<'_, K, Option<V>> {
        self.0.iter()
    }

}
impl<K, V> FromIterator<(K, Option<V>)> for OptionMap<K, V>
where
    K: Hash + Eq + Clone,
    V: Clone,
{
    fn from_iter<I: IntoIterator<Item = (K, Option<V>)>>(iterable: I) -> Self {
        let map = IndexMap::from_iter(iterable);
        OptionMap(map)
    }
}

impl<K, V, const N: usize> From<[(K, Option<V>); N]> for OptionMap<K, V>
where
    K: Hash + Eq + Clone,
    V: Clone
{
    fn from(arr: [(K, Option<V>); N]) -> Self {
        Self::from_iter(arr)
    }
}

impl<K, V> Extend<(K, Option<V>)> for OptionMap<K, V>
where
    K: Hash + Eq + Clone,
    V: Clone,
{
    fn extend<I: IntoIterator<Item = (K, Option<V>)>>(&mut self, iterable: I) {
        let iter = iterable.into_iter();
        let reserve = if self.0.is_empty() {
            iter.size_hint().0
        } else {
            (iter.size_hint().0 + 1) / 2
        };
        self.0.reserve(reserve);
        iter.for_each(move |(k, v)| {
            self.insert(k, v);
        });
    }
}

///////////////////////////////////////////////////////////////////////////////!SECTION
///
///
#[derive(Debug, Clone)]
pub struct L<T: Display+ Hash + Eq>(pub T, pub Offset);

impl<T: Display+ Hash + Eq> Display for L<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl<T: Display+ Hash + Eq> PartialEq for L<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl<T: Display+ Hash + Eq> Eq for L<T> {}
impl<T: Display+ Hash + Eq> Hash for L<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<T: Display+ Hash + Eq> L<T> {
    pub(crate) fn start(&self) -> Offset {
        self.1
    }
}