use std::collections::{
    hash_map::{IntoIter, Keys, Values},
    HashMap, HashSet,
};

use crate::{
    name::{Name, Ty},
    subst::{Subst, Substitutable},
    types::{Scheme, Type},
};

#[derive(Clone, Debug, Default)]
pub struct Envr {
    pub store: HashMap<Name, Scheme>,
}

/// Typing environment, represents a type scope. Essentially a wrapper for
/// a hashmap, this holds type names as keys, with their type schemes as values.
impl Envr {
    pub fn new() -> Envr {
        Envr {
            store: HashMap::default(),
        }
    }

    pub fn with_capacity(cap: usize) -> Envr {
        Envr {
            store: HashMap::with_capacity(cap),
        }
    }

    pub fn with_entries(entries: Vec<(Name, Scheme)>) -> Envr {
        let mut envr = Self::with_capacity(entries.len());
        for (k, v) in entries {
            envr.insert(k, v);
        }
        envr
    }

    pub fn singleton(name: Name, scheme: Scheme) -> Envr {
        Envr {
            store: HashMap::from([(name, scheme)]),
        }
    }

    /// Returns a type scheme S such that
    ///
    /// ```txt
    /// S = ftv(T) - ftv(E)
    ///   = forall { s in S } . T
    /// ```
    ///
    /// for the environment E
    pub fn generalize(&self, tipo: Type) -> Scheme {
        let poly = tipo.ftv().difference(&self.ftv()).cloned().collect();
        Scheme { poly, tipo }
    }

    pub fn contains_key(&self, k: &Name) -> bool {
        self.store.contains_key(k)
    }

    pub fn contains_value(&self, v: &Scheme) -> bool {
        self.store.iter().any(|(_, s)| s == v)
    }

    pub fn values(&self) -> Values<'_, Name, Scheme> {
        self.store.values()
    }

    pub fn get(&self, k: &Name) -> Option<&Scheme> {
        self.store.get(k)
    }

    pub fn set(&mut self, k: &Name) -> Option<&mut Scheme> {
        self.store.get_mut(k)
    }

    pub fn insert(&mut self, k: Name, v: Scheme) -> Option<Scheme> {
        self.store.insert(k, v)
    }

    pub fn insert_many(&mut self, entries: &[(Name, Scheme)]) -> &mut Envr {
        for (n, s) in entries {
            self.insert(*n, s.clone());
        }
        self
    }

    pub fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (Name, Scheme)>,
    {
        self.store.extend(iter);
    }

    pub fn clone_append(&mut self, k: Name, v: Scheme) -> Self {
        let mut env = self.clone();
        env.insert(k, v);
        env
    }

    pub fn remove(&mut self, k: &Name) -> Option<(Name, Scheme)> {
        self.store.remove_entry(k)
    }

    pub fn merge(&self, other: &Self) -> Envr {
        let store = self
            .store
            .iter()
            .chain(&other.store)
            .map(|(n, s)| (*n, s.clone()))
            .collect();
        Envr { store }
    }

    pub fn merge_all(&self, envs: &[Envr]) -> Envr {
        envs.iter().fold(self.clone(), |a, c| a.merge(c))
    }

    pub fn keys(&self) -> Keys<'_, Name, Scheme> {
        self.store.keys()
    }

    /// Return the union of two environments, with entries in the left (first;
    /// `self` receiver) environment taking precedence, i.e., `self`.
    pub fn union(&self, other: &Self) -> Envr {
        let keys = self.keys().chain(other.keys());
        let mut env = Envr::new();
        for k in keys {
            if let Some(v) = self.get(k) {
                env.insert(*k, v.clone());
            } else if let Some(v) = other.get(k) {
                env.insert(*k, v.clone());
            };
        }
        env
    }

    /// Returns an environment containing all entries found in both
    /// environments. Precedence is given to the receiver of this
    /// method, i.e., `self`.
    pub fn intersection(&self, other: &Self) -> Envr {
        let mut env = Envr::new();
        let keys = self.keys().chain(other.keys());
        for k in keys {
            if self.contains_key(k) && other.contains_key(k) {
                env.insert(*k, self.get(k).cloned().unwrap());
            }
        }
        env
    }

    /// Given another environment, returns a new environment containing
    /// all entries in the first not contained in the second.
    pub fn difference(&self, other: &Self) -> Envr {
        let mut env = self.clone();
        for k in other.keys() {
            env.remove(k);
        }
        env
    }
}

impl Substitutable for Envr {
    fn ftv(&self) -> HashSet<Ty> {
        self.values().cloned().collect::<Vec<_>>().ftv()
    }

    fn apply(&self, sub: &Subst) -> Self {
        self.store.iter().map(|(n, s)| (*n, s.apply(sub))).into()
    }
}

impl std::ops::Add for Envr {
    type Output = Envr;

    fn add(self, rhs: Self) -> Self::Output {
        self.merge(&rhs)
    }
}

impl std::ops::AddAssign for Envr {
    fn add_assign(&mut self, rhs: Self) {
        for (k, v) in rhs {
            self.insert(k, v);
        }
    }
}

impl<I> From<I> for Envr
where
    I: Iterator<Item = (Name, Scheme)>,
{
    fn from(iter: I) -> Self {
        let mut env = Envr::new();
        for (n, s) in iter {
            env.insert(n, s);
        }
        env
    }
}

impl From<Envr> for Vec<(Name, Scheme)> {
    fn from(envr: Envr) -> Self {
        envr.into_iter().collect()
    }
}

impl IntoIterator for Envr {
    type Item = (Name, Scheme);

    type IntoIter = IntoIter<Name, Scheme>;

    fn into_iter(self) -> Self::IntoIter {
        self.store.into_iter()
    }
}
