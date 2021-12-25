//! # Rust Small Database (RSDB)
//!
//! RSDB is a small library for creating a query-able database that is encoded with json.
//!
//! The library is well tested (~96.30% coverage according to [cargo-tarpaulin](https://crates.io/crates/cargo-tarpaulin)) and simple to use with
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
//! We can [search a database](search)...
//! ```
//! # use std::iter::FromIterator;
//! use rsdb::{Database, Query, search, search_mut, remove};
//! let db = Database::from_iter(1..10);
//! let found_items = search!(&db match |it: &i32| *it >= 5 && *it <= 7);
//! ```
//! ...[search a database (with mutable access)](search_mut)
//! ```
//! # use std::iter::FromIterator;
//! # use rsdb::{Database, Query, search, search_mut, remove};
//! # let mut db = Database::from_iter(1..10);
//! let found_items_mut1 = search_mut!(&mut db match |it: &i32| *it >= 5 && *it <= 7);
//! # std::mem::drop(found_items_mut1);
//! // or
//! let found_items_mut2 = search!(&mut db match |it: &i32| *it >= 5 && *it <= 7);
//! ```
//! ...and [remove items](remove) easily!
//! ```
//! # use std::iter::FromIterator;
//! # use rsdb::{Database, Query, search, search_mut, remove};
//! # let mut db = Database::from_iter(1..10);
//! let removed_items = remove!(&mut db match |it: &i32| *it >= 5 && *it <= 7);
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

#[cfg(test)]
use mutagen::mutate;
use serde;
use serde::de::DeserializeOwned;
use serde_derive::{Deserialize, Serialize};
use std::fs::File;
use std::io::{BufReader, BufWriter, Read, Write};
use std::ops::{BitAnd, BitOr};
use std::path::Path;
use thiserror::Error;

/// A type for declaring a function that takes some argument by reference and returns a boolean value.
type Predicate<T> = dyn Fn(&T) -> bool;

/// A sized [Predicate].
type BoxPredicate<T> = Box<Predicate<T>>;

/// Database error
#[derive(Error, Debug)]
pub enum DatabaseError {
    /// We could not parse json when loading from a file
    /// Raised in [Database::try_from].
    #[error("Had trouble parsing json database!")]
    BadJsonParse,
    /// We tried to use [Database::insert_unique] but the item already
    /// existed in the Database.
    #[error("Cannot insert duplicate items!")]
    DuplicateItemInsertion,
    /// We tried to write to a file with [Database::save_to_file] but was
    /// unsuccessful.
    #[error("Could not successfully write to writer!")]
    BadWrite,
}

/// A database stores many items in an unordered fashion.
///
/// ## Examples
///
/// We can create a database using any type.
/// ```
/// # use std::iter::FromIterator;
/// use rsdb::Database;
/// let db1: Database<i32> = Database::new();
/// let db2: Database<&u8> = Database::from_iter("hello world".as_bytes().into_iter());
/// struct Vec2 { x: i32, y: i32 };
/// let db3: Database<Vec2> = Database::from_iter(vec![ Vec2 { x: 0, y: 5 }, Vec2 { x: 100, y: 50 } ]);
/// ```
///
/// If the type is serializable, we can even save it as json!
/// ```no_run
/// # use std::error::Error;
/// # use std::iter::FromIterator;
/// # fn main() -> Result<(), Box<dyn Error>> {
/// use serde::{Serialize, Deserialize};
/// #[derive(Serialize, Deserialize)]
/// struct Vec2 { x: i32, y: i32 };
///
/// use rsdb::Database;
/// let db1: Database<i32> = Database::new();
/// let db2: Database<&u8> = Database::from_iter("hello world".as_bytes().into_iter());
/// let db3: Database<Vec2> = Database::from_iter(vec![ Vec2 { x: 0, y: 5 }, Vec2 { x: 100, y: 50 } ]);
///
/// db1.save_to_file("db1.json")?;
/// db2.save_to_file("db2.json")?;
/// db3.save_to_file("db3.json")?;
/// # Ok(())
/// # }
/// ```
///
/// We can query a database using macros!
///
/// We can [search a database](search)...
/// ```
/// # use std::iter::FromIterator;
/// use rsdb::{Database, Query, search, search_mut, remove};
/// let db = Database::from_iter(1..10);
/// let found_items = search!(&db match |it: &i32| *it >= 5 && *it <= 7);
/// ```
/// ...[search a database (with mutable access)](search_mut)
/// ```
/// # use std::iter::FromIterator;
/// # use rsdb::{Database, Query, search, search_mut, remove};
/// # let mut db = Database::from_iter(1..10);
/// let found_items_mut1 = search_mut!(&mut db match |it: &i32| *it >= 5 && *it <= 7);
/// # std::mem::drop(found_items_mut1);
/// // or
/// let found_items_mut2 = search!(&mut db match |it: &i32| *it >= 5 && *it <= 7);
/// ```
/// ...and [remove items](Database::remove) easily!
/// ```
/// # use std::iter::FromIterator;
/// # use rsdb::{Database, Query, search, search_mut, remove};
/// # let mut db = Database::from_iter(1..10);
/// let removed_items = remove!(&mut db match |it: &i32| *it >= 5 && *it <= 7);
/// ```
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default, Serialize, Deserialize)]
pub struct Database<T>(Vec<T>);

/// A query lets us check our database
/// ## Examples
/// [Searching a database](search)
/// ```
/// # use std::iter::FromIterator;
/// use rsdb::{Database, Query, search, search_mut, remove};
/// let db = Database::from_iter(1..10);
/// let found_items = search!(&db match |it: &i32| *it >= 5 && *it <= 7);
/// ```
/// ...[searching a database (with mutable access)](search_mut)
/// ```
/// # use std::iter::FromIterator;
/// # use rsdb::{Database, Query, search, search_mut, remove};
/// # let mut db = Database::from_iter(1..10);
/// let found_items_mut1 = search_mut!(&mut db match |it: &i32| *it >= 5 && *it <= 7);
/// # std::mem::drop(found_items_mut1);
/// // or even use
/// let found_items_mut2 = search!(&mut db match |it: &i32| *it >= 5 && *it <= 7);
/// ```
/// ...and [remove items](remove) easily!
/// ```
/// # use std::iter::FromIterator;
/// # use rsdb::{Database, Query, search, search_mut, remove};
/// # let mut db = Database::from_iter(1..10);
/// let removed_items = remove!(&mut db match |it: &i32| *it >= 5 && *it <= 7);
/// ```
/// If you don't want to use the macros, [queries][Query] can be composed together like so:
///
/// Simple query
/// ```
/// # use std::iter::FromIterator;
/// use rsdb::{Database, Query};
/// let db = Database::from_iter(1..10);
/// db.search(Query::new(|it: &i32| *it < 5));
/// ```
/// We can also chain together queries with the `&` and `|` operators
/// ```
/// # use std::iter::FromIterator;
/// # use rsdb::{Database, Query};
/// # let db = Database::from_iter(1..10);
/// // cool AND query
/// db.search( Query::new(|it: &i32| *it < 5) & Query::new(|it: &i32| *it > 2) );
/// // cool OR query
/// db.search( Query::new(|it: &i32| *it >= 5) | Query::new(|it: &i32| *it <= 2) );
/// ```
pub struct Query<T>(BoxPredicate<T>);

/// Generic library result returning something or [DatabaseError].
type Result<T> = core::result::Result<T, DatabaseError>;

impl<T> Query<T> {
    /// Allows us to create a new query from a predicate
    /// Try to use [search!](search), [search_mut!](search_mut), or [remove!](remove) instead of this,
    /// because it is smaller!
    #[cfg_attr(test, mutate)]
    pub fn new<P: 'static + Fn(&T) -> bool>(f: P) -> Self {
        Self(Box::new(f))
    }

    /// Check if this query accepts an item.
    /// Invalidates the query (Queries can only be called once)
    fn check(&self, it: &T) -> bool {
        self.0.call((it,))
    }
}

impl<T> Database<T> {
    /// We can search a database with a [Query]. Usually done with the [search!](search) macro.
    ///
    /// ## Examples
    /// Simple query
    /// ```
    /// # use std::iter::FromIterator;
    /// use rsdb::{Database, Query};
    /// let db = Database::from_iter(1..10);
    /// assert!([&1,&2,&3,&4].into_iter().eq(db.search(Query::new(|it: &i32| *it < 5))));
    /// ```
    /// We can also chain together queries with the `&` and `|` operators
    /// ```
    /// # use std::iter::FromIterator;
    /// # use rsdb::{Database, Query};
    /// # let mut db = Database::from_iter(1..10);
    /// // cool AND query
    /// assert!([&3,&4].into_iter().eq(
    ///     db.search( Query::new(|it: &i32| *it < 5) & Query::new(|it: &i32| *it > 2) )));
    /// // cool OR query
    /// assert!([&1,&2,&5,&6,&7,&8,&9].into_iter().eq(
    ///     db.search( Query::new(|it: &i32| *it >= 5) | Query::new(|it: &i32| *it <= 2) )));
    /// ```
    #[cfg_attr(test, mutate)]
    pub fn search(&self, query: Query<T>) -> impl Iterator<Item = &T> {
        self.0.iter().filter(move |it| query.check(it))
    }

    /// We can search a database with a [Query]. Usually done with the [search_mut!](search_mut) macro.
    ///
    /// ## Examples
    /// Simple query
    /// ```
    /// # use std::iter::FromIterator;
    /// use rsdb::{Database, Query};
    /// let mut db = Database::from_iter(1..10);
    /// assert!([&mut 1,&mut 2,&mut 3,&mut 4].into_iter().eq(
    ///     db.search_mut(Query::new(|it: &i32| *it < 5))));
    /// ```
    /// We can also chain together queries with the `&` and `|` operators
    /// ```
    /// # use std::iter::FromIterator;
    /// # use rsdb::{Database, Query};
    /// # let mut db = Database::from_iter(1..10);
    /// // cool AND query
    /// assert!([&mut 3,&mut 4].into_iter().eq(
    ///     db.search( Query::new(|it: &i32| *it < 5) & Query::new(|it: &i32| *it > 2) )));
    /// // cool OR query
    /// assert!([&mut 1,&mut 2,&mut 5,&mut 6,&mut 7,&mut 8,&mut 9].into_iter().eq(
    ///     db.search( Query::new(|it: &i32| *it > 4) | Query::new(|it: &i32| *it < 3) )));
    /// ```
    #[cfg_attr(test, mutate)]
    pub fn search_mut(&mut self, query: Query<T>) -> impl Iterator<Item = &mut T> {
        self.0.iter_mut().filter(move |it| query.check(it))
    }

    /// We can insert an item into a database
    ///
    /// ## Example
    /// ```
    /// use rsdb::Database;
    /// let mut db: Database<i32> = Database::new();
    /// db.insert(0);
    /// ```
    #[cfg_attr(test, mutate)]
    pub fn insert(&mut self, item: T) {
        self.0.push(item)
    }

    /// We can insert a unique item into a database
    /// ## Raises
    /// May raise an [DatabaseError::DuplicateItemInsertion] if trying to insert a duplicate item.
    /// ## Example
    /// ```
    /// use rsdb::Database;
    /// let mut db: Database<i32> = Database::new();
    /// assert!(db.insert_unique(0).is_ok());
    /// assert!(db.insert_unique(1).is_ok());
    /// assert!(db.insert_unique(0).is_err());
    /// assert!(db.insert_unique(1).is_err());
    /// assert!(db.insert_unique(2).is_ok());
    /// ```
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

    /// We can remove an item from a database with a [Query]. Usually done with [remove!](remove) macro.
    /// ## Examples
    /// Simple query
    /// ```
    /// # use std::iter::FromIterator;
    /// use rsdb::{Database, Query};
    /// let mut db = Database::from_iter(1..10);
    /// assert!([1,2,3,4].into_iter().eq(
    ///     db.remove(Query::new(|it: &i32| *it < 5))));
    /// assert!([&5,&6,&7,&8,&9].into_iter().eq(
    ///     db.iter()));
    /// ```
    #[cfg_attr(test, mutate)]
    pub fn remove(&mut self, query: Query<T>) -> impl Iterator<Item = T> + '_ {
        self.0.drain_filter(move |it| query.check(it))
    }

    /// Save the database to a Writer
    /// ## Raises:
    /// May raise a [DatabaseError::BadWrite] if we could not successfully write to the writer.
    /// ## Examples
    /// ```
    /// # use std::fmt::Write;
    /// # use std::iter::FromIterator;
    /// # use rsdb::Database;
    /// // given a simple writer
    /// struct StringWriter(String);
    /// impl std::io::Write for StringWriter {
    ///     fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
    ///         self.0.write_str(std::str::from_utf8(buf).unwrap()).unwrap();
    ///         Ok(buf.len())
    ///     }
    ///
    ///     fn flush(&mut self) -> std::io::Result<()> {
    ///         Ok(())
    ///     }
    /// }
    ///
    /// let db = Database::from_iter(1..10);
    /// let mut output = StringWriter { 0: String::new() };
    /// assert!(db.save(&mut output).is_ok());
    /// assert_eq!("[1,2,3,4,5,6,7,8,9]", output.0.as_str());
    /// ```
    #[cfg_attr(test, mutate)]
    pub fn save(&self, w: &mut dyn Write) -> Result<()>
    where
        T: serde::Serialize,
    {
        serde_json::to_writer(w, &self.0).map_err(|_| DatabaseError::BadWrite)
    }

    /// Allows us to save the database as json to a file.
    /// ## Raises:
    /// May raise a [DatabaseError::BadWrite] if we could not successfully write to the file.
    /// ## Examples:
    /// ```no_run
    /// # use std::iter::FromIterator;
    /// # use rsdb::DatabaseError;
    /// use rsdb::Database;
    /// # fn main() -> Result<(), DatabaseError> {
    /// let db: Database<i32> = Database::from_iter(1..10);
    /// db.save_to_file("test.db.json")?;
    /// # Ok(())
    /// # }
    /// ```
    #[cfg_attr(test, mutate)]
    pub fn save_to_file<P: AsRef<Path>>(&self, p: P) -> Result<()>
    where
        T: serde::Serialize,
    {
        let outfile = File::open(p).map_err(|_| DatabaseError::BadWrite)?;
        self.save(&mut BufWriter::new(outfile))
    }

    /// Lets us construct a new empty database.
    #[cfg_attr(test, mutate)]
    pub fn new() -> Self {
        Self { 0: Vec::new() }
    }

    /// Lets us see all the items in our database
    /// ## Examples
    /// ```
    /// # use std::iter::FromIterator;
    /// use rsdb::Database;
    /// let db: Database<i32> = Database::from_iter(1..10);
    /// for item in db.iter() {
    ///     println!("Item is {}!", item);
    /// }
    /// ```
    #[cfg_attr(test, mutate)]
    pub fn iter(&self) -> impl Iterator<Item = &T> + '_ {
        self.0.iter()
    }

    /// Allows us to see all of the items in our database and mutate them
    /// ## Examples
    /// ```
    /// # use std::iter::FromIterator;
    /// use rsdb::Database;
    /// let mut db: Database<i32> = Database::from_iter(1..10);
    /// for mut item in db.iter_mut() {
    ///     println!("Item was {}!", item);
    ///     *item += 5;
    ///     println!("Item is now {}!", item);
    /// }
    /// ```
    #[cfg_attr(test, mutate)]
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> + '_ {
        self.0.iter_mut()
    }
}

impl<T: 'static> BitAnd for Query<T> {
    type Output = Query<T>;

    fn bitand(self, rhs: Self) -> Self::Output {
        let f: BoxPredicate<T> = Box::new(move |it| self.check(it) && rhs.check(it));
        Self { 0: f }
    }
}

impl<T: 'static> BitOr for Query<T> {
    type Output = Query<T>;

    fn bitor(self, rhs: Self) -> Self::Output {
        let f: BoxPredicate<T> = Box::new(move |it| self.check(it) || rhs.check(it));
        Self { 0: f }
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

impl<T> Extend<T> for Database<T> {
    fn extend<It: IntoIterator<Item = T>>(&mut self, iter: It) {
        self.0.extend(iter)
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

/// A simple macro to remove an item from a database using a query
/// ## Examples
/// ```
/// # use std::iter::FromIterator;
/// use rsdb::{Database, Query, remove};
/// let mut db = Database::from_iter(1..10);
/// let removed_items = remove!(&mut db match |it: &i32| *it >= 5 && *it <= 7);
/// ```
#[macro_export]
macro_rules! remove {
    (&mut $db:ident match $p:expr) => {
        $db.remove(Query::new($p))
    };
}

/// A simple macro to search items in a database using a query
/// ## Examples
/// ```
/// # use std::iter::FromIterator;
/// use rsdb::{Database, Query, search};
/// let db = Database::from_iter(1..10);
/// let found_items = search!(&db match |it: &i32| *it >= 5 && *it <= 7);
/// ```
/// Also lets us get a mutable iterator
/// ```
/// # use std::iter::FromIterator;
/// use rsdb::{Database, Query, search};
/// let mut db = Database::from_iter(1..10);
/// let found_items = search!(&mut db match |it: &i32| *it < 5).for_each(|mut item| *item += 5);
/// ```
#[macro_export]
macro_rules! search {
    (&$db:ident match $p:expr) => {
        $db.search(Query::new($p))
    };
    (&mut $db:ident match $p:expr) => {
        $db.search_mut(Query::new($p))
    };
}

/// A simple macro to search items in a database (retaining a mutable reference) using a query
/// ## Examples
/// ```
/// # use std::iter::FromIterator;
/// use rsdb::{Database, Query, search_mut};
/// let mut db = Database::from_iter(1..10);
/// let found_items = search_mut!(&mut db match |it: &i32| *it < 5).for_each(|mut item| *item += 5);
/// ```
/// Also see [search]
#[macro_export]
macro_rules! search_mut {
    (&mut $db:ident match $p:expr) => {
        $db.search_mut(Query::new($p))
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
        let mut db =
            Database::from_iter([Coordinate::new(0, 0), Coordinate::new(0, 1)].into_iter());
        assert_eq!(
            search!(&db match |it: &Coordinate| it.x == it.y).collect::<Vec<&Coordinate>>(),
            vec![&Coordinate::new(0, 0)]
        );
        assert_eq!(
            search!(&mut db match |it: &Coordinate| it.x == it.y).collect::<Vec<&mut Coordinate>>(),
            vec![&mut Coordinate::new(0, 0)]
        );
    }

    #[test]
    fn test_search_mut_macro() {
        let mut db =
            Database::from_iter([Coordinate::new(0, 0), Coordinate::new(0, 1)].into_iter());
        assert_eq!(
            search_mut!(&mut db match |it: &Coordinate| it.x == it.y)
                .collect::<Vec<&mut Coordinate>>(),
            vec![&mut Coordinate::new(0, 0)]
        );
    }

    #[test]
    fn test_remove_macro() {
        let mut db =
            Database::from_iter([Coordinate::new(0, 0), Coordinate::new(0, 1)].into_iter());
        assert_eq!(
            remove!(&mut db match |it: &Coordinate| it.x == it.y).collect::<Vec<Coordinate>>(),
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
        assert_eq!(vec![1], db.into_iter().collect::<Vec<i32>>())
    }

    #[test]
    fn test_extend() {
        let mut db = Database::<i32>::from_iter(1..5);
        db.extend(5..10);
        assert!(Vec::from_iter(1..10).iter().eq(db.iter()));
    }

    #[test]
    fn test_from_vec() {
        let db = Database::from(vec![1, 2, 3, 4, 5]);
        assert!(vec![1, 2, 3, 4, 5].iter().eq(db.iter()));
    }
}
