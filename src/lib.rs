// TODO add doc comments
#![feature(drain_filter)]

use serde::de::DeserializeOwned;
use serde::Serialize;
use std::fs::File;
use std::io::{BufReader, BufWriter, Read, Write};
use std::ops::Add;
use std::path::Path;
use thiserror::Error;

type Predicate<T> = dyn Fn(&T) -> bool;

#[derive(Error, Debug)]
pub enum DatabaseError {
    #[error("Had trouble parsing json database!")]
    BadJsonParse,
    #[error("Cannot insert duplicate items!")]
    DuplicateItemInsertion,
    #[error("Could not successfully write to writer!")]
    BadWrite,
}

pub struct Database<T>(Vec<T>);
pub struct Query<T>(Vec<Box<Predicate<T>>>);

type Result<T> = core::result::Result<T, DatabaseError>;

impl<T> Query<T> {
    pub fn new<P: for<'a> Fn(&'a T) -> bool + 'static>(f: P) -> Self {
        Self(vec![Box::new(f)])
    }

    fn check(&self, it: &T) -> bool {
        self.0.iter().map(|f| f(it)).all(|b| b)
    }
}

impl<T> Database<T> {
    pub fn search(&self, query: Query<T>) -> impl Iterator<Item = &T> {
        self.0.iter().filter(move |it| query.check(it))
    }

    pub fn search_mut(&mut self, query: Query<T>) -> impl Iterator<Item = &mut T> {
        self.0.iter_mut().filter(move |it| query.check(it))
    }

    pub fn insert(&mut self, item: T) {
        self.0.push(item)
    }

    pub fn insert_unique(&mut self, item: T) -> Result<()>
    where
        T: PartialEq,
    {
        if self.0.contains(&item) {
            Err(DatabaseError::DuplicateItemInsertion)
        } else {
            self.0.push(item);
            Ok(())
        }
    }

    pub fn remove(&mut self, query: Query<T>) -> impl Iterator<Item = T> + '_ {
        self.0.drain_filter(move |it| query.check(it))
    }

    pub fn save<W: Write>(&self, w: W) -> Result<()>
    where
        T: Serialize,
    {
        serde_json::to_writer(w, &self.0).map_err(|_| DatabaseError::BadWrite)
    }

    pub fn save_to_file<P: AsRef<Path>>(&self, p: P) -> Result<()>
    where
        T: Serialize,
    {
        let outfile = File::open(p).map_err(|_| DatabaseError::BadWrite)?;
        self.save(BufWriter::new(outfile))
    }

    pub fn new() -> Self {
        Self { 0: Vec::new() }
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> + '_ {
        self.0.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> + '_ {
        self.0.iter_mut()
    }
}

impl<T> Default for Database<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Add for Query<T> {
    type Output = Query<T>;

    fn add(self, rhs: Self) -> Self::Output {
        let mut v = self.0;
        let mut v2 = rhs.0;
        v.append(&mut v2);
        Self(v)
    }
}

impl<R: Read, T: DeserializeOwned> TryFrom<BufReader<R>> for Database<T> {
    type Error = DatabaseError;

    fn try_from(r: BufReader<R>) -> Result<Self> {
        let data = serde_json::from_reader(r).map_err(|_| DatabaseError::BadJsonParse)?;
        Ok(Self { 0: data })
    }
}

impl<T> FromIterator<T> for Database<T> {
    fn from_iter<It: IntoIterator<Item = T>>(iter: It) -> Self {
        Self {
            0: Vec::from_iter(iter),
        }
    }
}

impl<T> IntoIterator for Database<T> {
    type Item = T;
    type IntoIter = <std::vec::Vec<T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test_search() {
        let db = Database::from_iter(1..10);
        type Q = Query<i32>;
        assert!(vec![&4, &6]
            .into_iter()
            .eq(db.search(Q::new(|it| *it > 3) + Q::new(|it| *it < 7) + Q::new(|it| *it != 5))));
    }

    #[test]
    fn test_insert() {
        let mut db = Database::new();
        db.insert(1);
        db.insert(2);
        db.insert(3);
        db.insert(1);
        db.insert(2);
        db.insert(3);
        assert!(vec![&1, &2, &3, &1, &2, &3]
            .into_iter()
            .eq(db.search(Query::new(|_| true))));
    }

    #[test]
    fn test_insert_unique() {
        let mut db = Database::new();
        db.insert(1);
        db.insert(2);
        db.insert_unique(3).ok();
        db.insert_unique(1).err();
    }

    #[test]
    fn test_search_mut() {
        let mut db = Database::from_iter(1..10);
        type Q = Query<i32>;
        db.search_mut(Q::new(|it| *it < 5)).for_each(|it| *it += 5);
        assert!(vec![6, 7, 8, 9, 5, 6, 7, 8, 9]
            .into_iter()
            .eq(db.into_iter()))
    }

    #[test]
    fn test_delete() {
        let mut db = Database::from_iter(1..10);
        type Q = Query<i32>;
        assert!(vec![1, 2, 3, 4]
            .into_iter()
            .eq(db.remove(Q::new(|it| *it < 5))));
        assert!(vec![5, 6, 7, 8, 9].into_iter().eq(db.into_iter()));
    }

    #[test]
    fn test_iter() {
        let mut db = Database::from_iter(1..10);
        assert!(Vec::from_iter(1..10).iter().eq(db.iter()))
    }

    #[test]
    fn test_iter_mut() {
        let mut db = Database::from_iter(1..10);
        db.iter_mut().for_each(|it| *it += 5);
        let mut vec = Vec::from_iter(1..10);
        vec.iter_mut().for_each(|it| *it += 5);
        assert!(vec.iter().eq(db.iter()))
    }
}
