// TODO add doc comments
#![feature(drain_filter)]
#![feature(fn_traits)]

use serde::de::DeserializeOwned;
use serde::Serialize;
use std::fs::File;
use std::io::{BufReader, BufWriter, Read, Write};
use std::ops::{BitAnd, BitOr};
use std::path::Path;
use thiserror::Error;
#[cfg(test)]
use mutagen::mutate;

type Predicate<T> = dyn Fn(&T) -> bool;
type BoxPredicate<T> = Box<Predicate<T>>;

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
pub struct Query<T>(Vec<BoxPredicate<T>>);

type Result<T> = core::result::Result<T, DatabaseError>;

impl<T> Query<T> {
    #[cfg_attr(test, mutate)]
    pub fn new<P: 'static + Fn(&T) -> bool>(f: P) -> Self {
        Self(vec![Box::new(f)])
    }

    fn check(&self, it: &T) -> bool {
        self.0.iter().map(move |f| f(it)).all(|b| b)
    }
}

impl<T> Database<T> {
    #[cfg_attr(test, mutate)]
    pub fn search(&self, query: Query<T>) -> impl Iterator<Item = &T> {
        self.0.iter().filter(move |it| query.check(it))
    }

    #[cfg_attr(test, mutate)]
    pub fn search_mut(&mut self, query: Query<T>) -> impl Iterator<Item = &mut T> {
        self.0.iter_mut().filter(move |it| query.check(it))
    }

    #[cfg_attr(test, mutate)]
    pub fn insert(&mut self, item: T) {
        self.0.push(item)
    }

    #[cfg_attr(test, mutate)]
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

    #[cfg_attr(test, mutate)]
    pub fn remove(&mut self, query: Query<T>) -> impl Iterator<Item = T> + '_ {
        self.0.drain_filter(move |it| query.check(it))
    }

    #[cfg_attr(test, mutate)]
    pub fn save(&self, w: &mut dyn Write) -> Result<()>
    where
        T: Serialize,
    {
        serde_json::to_writer(w, &self.0).map_err(|_| DatabaseError::BadWrite)
    }

    #[cfg_attr(test, mutate)]
    pub fn save_to_file<P: AsRef<Path>>(&self, p: P) -> Result<()>
    where
        T: Serialize,
    {
        let outfile = File::open(p).map_err(|_| DatabaseError::BadWrite)?;
        self.save(&mut BufWriter::new(outfile))
    }

    #[cfg_attr(test, mutate)]
    pub fn new() -> Self {
        Self { 0: Vec::new() }
    }

    #[cfg_attr(test, mutate)]
    pub fn iter(&self) -> impl Iterator<Item = &T> + '_ {
        self.0.iter()
    }

    #[cfg_attr(test, mutate)]
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> + '_ {
        self.0.iter_mut()
    }
}

impl<T> Default for Database<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: 'static> BitAnd for Query<T> {
    type Output = Query<T>;

    fn bitand(self, rhs: Self) -> Self::Output {
        let f: BoxPredicate<T> = Box::new(move |it| self.check(it) && rhs.check(it));
        Self { 0: vec![f] }
    }
}

impl<T: 'static> BitOr for Query<T> {
    type Output = Query<T>;

    fn bitor(self, rhs: Self) -> Self::Output {
        let f: BoxPredicate<T> = Box::new(move |it| self.check(it) || rhs.check(it));
        Self { 0: vec![f] }
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
    use serde_derive::{Deserialize, Serialize};
    use std::fmt::Write;

    #[test]
    fn test_search() {
        let db = Database::from_iter(1..10);
        type Q = Query<i32>;
        assert_eq!(
            vec![&4, &6],
            db.search(Q::new(|it| *it > 3) & Q::new(|it| *it < 7) & Q::new(|it| *it != 5))
                .collect::<Vec<&i32>>()
        );
        assert_eq!(
            vec![&1, &2, &3, &5, &7, &8, &9],
            db.search(Q::new(|it| *it <= 3) | Q::new(|it| *it >= 7) | Q::new(|it| *it == 5))
                .collect::<Vec<&i32>>()
        );
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
        assert!(db.insert_unique(3).is_ok());
        assert!(db.insert_unique(1).is_err());
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
        let db = Database::from_iter(1..10);
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

    // set up small mocking for writer
    struct StringWriter(String);
    impl std::io::Write for StringWriter {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.0.write_str(std::str::from_utf8(buf).unwrap()).unwrap();
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn test_save() {
        let db = Database::from_iter(1..10);
        let mut output = StringWriter { 0: String::new() };
        assert!(db.save(&mut output).is_ok());
        assert_eq!("[1,2,3,4,5,6,7,8,9]", output.0.as_str());
    }

    #[derive(Serialize, Deserialize, Debug)]
    struct Coordinate {
        x: i32,
        y: i32,
    }

    impl Coordinate {
        #[cfg_attr(test, mutate)]
        pub fn new(x: i32, y: i32) -> Self {
            Self { x, y }
        }
    }

    #[test]
    fn test_save_complex() {
        let db = Database::from_iter([Coordinate::new(0, 0), Coordinate::new(1, 1)].into_iter());
        let mut output = StringWriter { 0: String::new() };
        assert!(db.save(&mut output).is_ok());
        assert_eq!(r#"[{"x":0,"y":0},{"x":1,"y":1}]"#, output.0.as_str());
    }
}
