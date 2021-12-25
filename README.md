# Tiny Query Database (TQDB)

TQDB is a small library for creating a query-able database that is encoded with json.

The library is well tested (~96.30% coverage according to [cargo-tarpaulin](https://crates.io/crates/cargo-tarpaulin)) 
and simple to use with the help of macros.

## Examples

We can create a database using any type.
```rs
use tqdb::Database;
let db1: Database<i32> = Database::new();
let db2: Database<&u8> = Database::from_iter("hello world".as_bytes().into_iter());
struct Vec2 { x: i32, y: i32 };
let db3: Database<Vec2> = Database::from_iter(vec![ Vec2 { x: 0, y: 5 }, Vec2 { x: 100, y: 50 } ]);
```

If the type is serializable, we can even save it as json!
```rs
use serde::{Serialize, Deserialize};
struct Vec2 { x: i32, y: i32 };
 
use tqdb::Database;
let db1: Database<i32> = Database::new();
let db2: Database<&u8> = Database::from_iter("hello world".as_bytes().into_iter());
let db3: Database<Vec2> = Database::from_iter(vec![ Vec2 { x: 0, y: 5 }, Vec2 { x: 100, y: 50 } ]);
 
db1.save_to_file("db1.json")?;
db2.save_to_file("db2.json")?;
db3.save_to_file("db3.json")?;
```

We can query a database using macros!

We can search a database...
```rs
use tqdb::{Database, Query, search, search_mut, remove};
let db = Database::from_iter(1..10);
let found_items = search!(&db match |it: &i32| *it >= 5 && *it <= 7);
```
...search a database (with mutable access)
```rs
let found_items_mut1 = search_mut!(&mut db match |it: &i32| *it >= 5 && *it <= 7);
// or
let found_items_mut2 = search!(&mut db match |it: &i32| *it >= 5 && *it <= 7);
```
...and remove items easily!
```rs
let removed_items = remove!(&mut db match |it: &i32| *it >= 5 && *it <= 7);
```
If you don't want to use the macros, queries can be composed together like so:
```rs
use tqdb::{Database, Query};
let db = Database::from_iter(1..10);
// boring, simple query
db.search(Query::new(|it: &i32| *it < 5));
// cool AND query
db.search( Query::new(|it: &i32| *it < 5) & Query::new(|it: &i32| *it > 2) );
// cool OR query
db.search( Query::new(|it: &i32| *it >= 5) | Query::new(|it: &i32| *it <= 2) );
```