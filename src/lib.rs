//! # Rust Small Database (RSDB)
//!
//! RSDB is a small library for creating a query-able database that is encoded with json.
//!
//! The library is well tested (~95.74% coverage) and simple to use with
//! macros.
//!
//! ## Examples
//!
//! We can create a [database][d] using any type.
//! ```
//! # use std::iter::FromIterator;
//! use rsdb::Database;
//! let db1: Database<i32> = Database::new();
//! let db2: Database<&u8> = Database::from_iter("hello world".as_bytes().into_iter());
//! struct Vec2 { x: i32, y: i32 };
//! let db3: Database<Vec2> = Database::from_iter(vec![ Vec2 { x: 0, y: 5 }, Vec2 { x: 100, y: 50 } ]);
//! ```
//!
//! If the type is serializable, we can even save it as json!
//! ```no_run
//! # use std::error::Error;
//! # use std::iter::FromIterator;
//! # fn main() -> Result<(), Box<dyn Error>> {
//! use serde::{Serialize, Deserialize};
//! #[derive(Serialize, Deserialize)]
//! struct Vec2 { x: i32, y: i32 };
//!
//! use rsdb::Database;
//! let db1: Database<i32> = Database::new();
//! let db2: Database<&u8> = Database::from_iter("hello world".as_bytes().into_iter());
//! let db3: Database<Vec2> = Database::from_iter(vec![ Vec2 { x: 0, y: 5 }, Vec2 { x: 100, y: 50 } ]);
//!
//! db1.save_to_file("db1.json")?;
//! db2.save_to_file("db2.json")?;
//! db3.save_to_file("db3.json")?;
//! # Ok(())
//! # }
//! ```
//!
//! We can query a [database][d] using macros!
//!
//! We can [search](Database::search)...
//! ```
//! # use std::iter::FromIterator;
//! use rsdb::{Database, Query, search, search_mut, remove};
//! let mut db = Database::from_iter(1..10);
//! let found_items = search!(db with |it: &i32| *it >= 5 && *it <= 7);
//! ```
//! ...[search (with mutable access)](Database::search_mut)
//! ```
//! # use std::iter::FromIterator;
//! # use rsdb::{Database, Query, search, search_mut, remove};
//! # let mut db = Database::from_iter(1..10);
//! let found_items_mut = search_mut!(db with |it: &i32| *it >= 5 && *it <= 7);
//! ```
//! ...and [remove](Database::remove) items easily!
//! ```
//! # use std::iter::FromIterator;
//! # use rsdb::{Database, Query, search, search_mut, remove};
//! # let mut db = Database::from_iter(1..10);
//! let removed_items = remove!(db with |it: &i32| *it >= 5 && *it <= 7);
//! ```
//! There is even a [query!](query) macro that does all three of these functions for increased readability!
//! ```compile_fail
//! # use std::iter::FromIterator;
//! # use rsdb::{Database, Query, query, search, search_mut, remove};
//! # let mut db = Database::from_iter(1..10);
//! // query! macro lets us combine the above three for an easy-to-read syntax
//! let found_items     = query!(db search |&it: &i32| it >= 5 && it <= 7);     // search!
//! let found_items_mut = query!(mut db search |&it: &i32| it >= 5 && it <= 7); // search_mut!
//! let removed_items   = query!(db remove |&it: &i32| it >= 5 && it <= 7);     // remove!
//! ```
//! If you don't want to use the macros, [queries][q] can be composed together like so:
//! ```
//! # use std::iter::FromIterator;
//! use rsdb::{Database, Query};
//! let db = Database::from_iter(1..10);
//! // boring, simple query
//! db.search(Query::new(|it: &i32| *it < 5));
//! // cool AND query
//! db.search( Query::new(|it: &i32| *it < 5) & Query::new(|it: &i32| *it > 2) );
//! // cool OR query
//! db.search( Query::new(|it: &i32| *it >= 5) | Query::new(|it: &i32| *it <= 2) );
//! ```
//! [d]: Database
//! [q]: Query

#![feature(drain_filter)]
#![feature(fn_traits)]
#![feature(no_coverage)]

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

/// A database is simply a vector of items
#[derive(Eq, PartialEq, Debug)]
pub struct Database<T>(Vec<T>);

/// A query lets us
pub struct Query<T>(Vec<BoxPredicate<T>>);

/// Generic library result returning something or [DatabaseError].
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
    /// We can search a database with a query. Usually done with the `search!` macro.
    #[cfg_attr(test, mutate)]
    pub fn search(&self, query: Query<T>) -> impl Iterator<Item=&T> {
        self.0.iter().filter(move |it| query.check(it))
    }

    #[cfg_attr(test, mutate)]
    pub fn search_mut(&mut self, query: Query<T>) -> impl Iterator<Item=&mut T> {
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
    pub fn remove(&mut self, query: Query<T>) -> impl Iterator<Item=T> + '_ {
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
    pub fn iter(&self) -> impl Iterator<Item=&T> + '_ {
        self.0.iter()
    }

    #[cfg_attr(test, mutate)]
    pub fn iter_mut(&mut self) -> impl Iterator<Item=&mut T> + '_ {
        self.0.iter_mut()
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

impl<T> Default for Database<T> {
    fn default() -> Self {
        Self::new()
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
    fn from_iter<It: IntoIterator<Item=T>>(iter: It) -> Self {
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

impl<T> From<Vec<T>> for Database<T> {
    fn from(v: Vec<T>) -> Self {
        Self { 0: v }
    }
}

#[macro_export]
macro_rules! remove {
    ($db:ident with $p:expr) => {
        $db.remove(Query::new($p))
    }
}

#[macro_export]
macro_rules! search {
    ($db:ident with $p:expr) => {
        $db.search(Query::new($p))
    }
}

#[macro_export]
macro_rules! search_mut {
    ($db:ident with $p:expr) => {
        $db.search_mut(Query::new($p))
    }
}

#[macro_export]
macro_rules! query {
    ($db:ident search $p:expr) => {
        search!($db with $p)
    };
    (mut $db:ident search $p:expr) => {
        search_mut!($db with $p)
    };
    ($db:ident remove $p:expr) => {
        remove!($db with $p)
    };
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

        #[no_coverage]
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

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
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

    #[test]
    fn test_search_macro() {
        let db = Database::from_iter([Coordinate::new(0, 0), Coordinate::new(0, 1)].into_iter());
        assert_eq!(
            search!(db with |it: &Coordinate| it.x == it.y).collect::<Vec<&Coordinate>>(),
            vec![&Coordinate::new(0, 0)]
        );
    }

    #[test]
    fn test_search_mut_macro() {
        let mut db = Database::from_iter([Coordinate::new(0, 0), Coordinate::new(0, 1)].into_iter());
        assert_eq!(
            search_mut!(db with |it: &Coordinate| it.x == it.y).collect::<Vec<&mut Coordinate>>(),
            vec![&mut Coordinate::new(0, 0)]
        );
    }

    #[test]
    fn test_remove_macro() {
        let mut db = Database::from_iter([Coordinate::new(0, 0), Coordinate::new(0, 1)].into_iter());
        assert_eq!(
            remove!(db with |it: &Coordinate| it.x == it.y).collect::<Vec<Coordinate>>(),
            vec![Coordinate::new(0, 0)]
        );
        assert_eq!(
            db.iter().collect::<Vec<&Coordinate>>(),
            vec![&mut Coordinate::new(0, 1)]
        );
    }

    #[test]
    fn test_query_macro() {
        let mut db = Database::from_iter([Coordinate::new(0, 0), Coordinate::new(0, 1)].into_iter());
        assert_eq!(
            query!(db search |it: &Coordinate| it.x == it.y).collect::<Vec<&Coordinate>>(),
            vec![&Coordinate::new(0, 0)]
        );
        assert_eq!(
            query!(mut db search |it: &Coordinate| it.x == it.y).collect::<Vec<&mut Coordinate>>(),
            vec![&mut Coordinate::new(0, 0)]
        );
        assert_eq!(
            query!(db remove |it: &Coordinate| it.x == it.y).collect::<Vec<Coordinate>>(),
            vec![Coordinate::new(0, 0)]
        );
        assert_eq!(
            db.iter().collect::<Vec<&Coordinate>>(),
            vec![&mut Coordinate::new(0, 1)]
        );
    }

    #[test]
    fn test_default() {
        let mut db = Database::<i32>::default();
        assert!(db.insert_unique(1).is_ok());
        assert_eq!(
            vec![1],
            db.into_iter().collect::<Vec<i32>>()
        )
    }
}
