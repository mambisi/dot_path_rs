use serde::de::DeserializeOwned;
use serde::Serialize;
use serde_json::{Map, Value};
use std::cmp::Ordering;
use std::mem;

/// Access and mutate nested JSON elements by dotted paths
///
/// The path is composed of keys separated by dots, e.g. `foo.bar.1`.
///
/// Arrays are indexed by numeric strings or special keys (see `dot_get()` and `dot_set()`).
///
/// This trait is implemented for `serde_json::Value`, specifically the
/// `Map`, `Array`, and `Null` variants. Empty path can also be used to access a scalar.
pub trait DotPaths {
    /// Get an item by path, if present.
    ///
    /// JSON `null` becomes `None`, same as unpopulated path.
    ///
    /// # Special keys
    /// Arrays can be indexed by special keys for reading:
    /// - `>` ... last element
    ///
    /// # Panics
    /// - If the path attempts to index into a scalar (e.g. `"foo.bar"` in `{"foo": 123}`)
    /// - If the path uses invalid key in an array or map
    fn dot_get<T>(&self, path: &str) -> Option<T>
    where
        T: DeserializeOwned;

    /// Get an item, or a default value.
    ///
    /// # Special keys
    /// see `dot_get()`
    ///
    /// # Panics
    /// see `dot_get()`
    fn dot_get_or<T>(&self, path: &str, def: T) -> T
    where
        T: DeserializeOwned,
    {
        self.dot_get(path).unwrap_or(def)
    }

    /// Get an item, or a default value using the Default trait
    ///
    /// # Special keys
    /// see `dot_get()`
    ///
    /// # Panics
    /// see `dot_get()`
    fn dot_get_or_default<T>(&self, path: &str) -> T
    where
        T: DeserializeOwned + Default,
    {
        self.dot_get(path).unwrap_or_default()
    }

    /// Get a mutable reference to an item
    ///
    /// # Special keys
    /// see `dot_get()`
    ///
    /// # Panics
    /// see `dot_get()`
    fn dot_get_mut(&mut self, path: &str) -> Option<&mut Value>;

    /// Insert an item by path.
    ///
    /// # Special keys
    /// Arrays can be indexed by special keys:
    /// - `+` or `>` ... append
    /// - `-` or `<` ... prepend
    /// - `>n` ... insert after an index `n`
    /// - `<n` ... insert before an index `n`
    ///
    /// # Panics
    /// see `dot_get()`
    fn dot_set<T>(&mut self, path: &str, value: T)
    where
        T: Serialize;

    /// Replace a value by path with a new value.
    /// The value types do not have to match.
    ///
    /// # Panics
    /// see `dot_get()`
    fn dot_replace<T, U>(&mut self, path: &str, value: T) -> Option<U>
    where
        T: Serialize,
        U: DeserializeOwned;

    /// Get an item using a path, removing it from the store.
    /// If no item was stored under this path, then None is returned.
    ///
    /// # Panics
    /// see `dot_get()`
    fn dot_take<T>(&mut self, path: &str) -> Option<T>
    where
        T: DeserializeOwned;

    /// Remove an item matching a key.
    /// Returns true if any item was removed.
    ///
    /// # Panics
    /// see `dot_get()`
    fn dot_remove(&mut self, path: &str) -> bool {
        self.dot_take::<Value>(path).is_some()
    }
}

/// Split the path string by dot, if present.
///
/// Returns a tuple of (before_dot, after_dot)
fn path_split(path: &str) -> (&str, Option<&str>) {
    let dot = path.find('.');
    match dot {
        None => (path, None),
        Some(pos) => (&path[0..pos], Some(&path[pos + 1..])),
    }
}

impl DotPaths for serde_json::Value {
    fn dot_get<T>(&self, path: &str) -> Option<T>
    where
        T: DeserializeOwned,
    {
        match self {
            Value::Array(vec) => vec.dot_get(path),
            Value::Object(map) => map.dot_get(path),
            Value::Null => None,
            _ => {
                if path.is_empty() {
                    serde_json::from_value(self.to_owned()).ok()
                } else {
                    panic!("Node is not array or object!");
                }
            }
        }
    }

    fn dot_get_mut(&mut self, path: &str) -> Option<&mut Value> {
        match self {
            Value::Array(vec) => vec.dot_get_mut(path),
            Value::Object(map) => map.dot_get_mut(path),
            Value::Null => None,
            _ => {
                if path.is_empty() {
                    Some(self)
                } else {
                    panic!("Node is not array or object!");
                }
            }
        }
    }

    fn dot_set<T>(&mut self, path: &str, value: T)
    where
        T: Serialize,
    {
        match self {
            Value::Array(vec) => {
                vec.dot_set(path, value);
            }
            Value::Object(map) => {
                map.dot_set(path, value);
            }
            Value::Null => {
                mem::replace(self, new_by_path_root(path, value));
            }
            _ => {
                if path.is_empty() {
                    mem::replace(self, serde_json::to_value(value).expect("Serialize error"));
                } else {
                    panic!("Node is not an array, object, or null!");
                }
            }
        }
    }

    fn dot_replace<T, U>(&mut self, path: &str, value: T) -> Option<U>
    where
        T: Serialize,
        U: DeserializeOwned,
    {
        match self {
            Value::Array(vec) => vec.dot_replace(path, value),
            Value::Object(map) => map.dot_replace(path, value),
            Value::Null => {
                self.dot_set(path, value);
                None
            }
            _ => {
                if path.is_empty() {
                    let new = serde_json::to_value(value).expect("Serialize error");
                    let old = mem::replace(self, new);
                    Some(serde_json::from_value(old).expect("Unserialize error"))
                } else {
                    panic!("Node is not an array, object, or null!")
                }
            }
        }
    }

    fn dot_take<T>(&mut self, path: &str) -> Option<T>
    where
        T: DeserializeOwned,
    {
        match self {
            Value::Array(vec) => vec.dot_take(path),
            Value::Object(map) => map.dot_take(path),
            Value::Null => None,
            _ => {
                if path.is_empty() {
                    let old = mem::replace(self, Value::Null);
                    Some(serde_json::from_value(old).expect("Unserialize error"))
                } else {
                    panic!("Node is not an array, object, or null!")
                }
            }
        }
    }
}

/// Create a Value::Object or Value::Array based on a nested path.
///
/// Builds the parent path to a non-existent key in set-type operations.
fn new_by_path_root<T>(path: &str, value: T) -> Value
where
    T: Serialize,
{
    if path.is_empty() {
        return serde_json::to_value(value).expect("Serialize error");
    }

    let (sub1, _) = path_split(path);
    if sub1 == "0" || sub1 == "+" || sub1 == "<" || sub1 == ">" {
        // new vec
        let mut new_vec = vec![];
        new_vec.dot_set(path, value);
        Value::Array(new_vec)
    } else {
        // new map
        let mut new_map = Map::new();
        new_map.dot_set(path, value);
        Value::Object(new_map)
    }
}

/// Check if a key is valid to use by dot paths in Value::Object.
/// The key must start with an alpha character or underscore and must not contain period.
fn validate_map_key(key: &str) {
    if key.parse::<usize>().is_ok() {
        panic!("Numeric keys are not allowed in maps: {}", key);
    }

    if !key.starts_with(|p: char| p.is_ascii_alphabetic() || p == '_') || key.contains('.') {
        panic!("Invalid map key: {}", key);
    }
}

impl DotPaths for serde_json::Map<String, serde_json::Value> {
    fn dot_get<T>(&self, path: &str) -> Option<T>
    where
        T: DeserializeOwned,
    {
        let (my, sub) = path_split(path);
        validate_map_key(my);

        if let Some(sub_path) = sub {
            self.get(my)
                .map(|child| child.dot_get(sub_path)) // this produces Option<Option<T>>
                .unwrap_or_default()
        } else {
            self.get(my)
                .map(ToOwned::to_owned)
                .map(serde_json::from_value)
                .transpose() // Option<Result> to Result<Option>
                .unwrap_or_default() // get rid of the result
        }
    }

    fn dot_get_mut(&mut self, path: &str) -> Option<&mut Value> {
        let (my, sub) = path_split(path);
        validate_map_key(my);

        if let Some(sub_path) = sub {
            self.get_mut(my)
                .map(|m| m.get_mut(sub_path))
                .unwrap_or_default()
        } else {
            self.get_mut(my)
        }
    }

    fn dot_set<T>(&mut self, path: &str, value: T)
    where
        T: Serialize,
    {
        let (my, sub) = path_split(path);
        validate_map_key(my);

        if let Some(subpath) = sub {
            if self.contains_key(my) {
                self.get_mut(my).unwrap().dot_set(subpath, value);
            } else {
                self.insert(my.into(), new_by_path_root(subpath, value));
            }
        } else {
            let packed = serde_json::to_value(value).expect("Serialize error");
            self.insert(my.into(), packed);
        }
    }

    fn dot_replace<T, U>(&mut self, path: &str, value: T) -> Option<U>
    where
        T: Serialize,
        U: DeserializeOwned,
    {
        let (my, sub) = path_split(path);
        validate_map_key(my);

        if let Some(subpath) = sub {
            if self.contains_key(my) {
                self.get_mut(my).unwrap().dot_replace(subpath, value)
            } else {
                self.dot_set(path, value);
                None
            }
        } else {
            let packed = serde_json::to_value(value).expect("Serialize error");
            self.insert(my.to_string(), packed)
                .map(serde_json::from_value)
                .transpose()
                .expect("Unserialize error")
        }
    }

    fn dot_take<T>(&mut self, path: &str) -> Option<T>
    where
        T: DeserializeOwned,
    {
        let (my, sub) = path_split(path);
        validate_map_key(my);

        if let Some(subpath) = sub {
            if let Some(item) = self.get_mut(my) {
                item.dot_take(subpath)
            } else {
                None
            }
        } else {
            self.remove(my)
                .map(serde_json::from_value)
                .transpose() // Option<Result> to Result<Option>
                .expect("Unserialize error") // get rid of the result
        }
    }
}

impl DotPaths for Vec<serde_json::Value> {
    fn dot_get<T>(&self, path: &str) -> Option<T>
    where
        T: DeserializeOwned,
    {
        let (my, sub) = path_split(path);

        let index: usize = if my == ">" {
            self.len() - 1
        } else {
            my.parse().unwrap()
        };

        if let Some(subpath) = sub {
            self.get(index)
                .map(ToOwned::to_owned)
                .map(|child| child.dot_get(subpath))
                .unwrap_or_default()
        } else {
            self.get(index)
                .map(ToOwned::to_owned)
                .map(serde_json::from_value)
                .transpose()
                .unwrap_or_default()
        }
    }

    fn dot_get_mut(&mut self, path: &str) -> Option<&mut Value> {
        let (my, sub) = path_split(path);

        let my: usize = my
            .parse()
            .unwrap_or_else(|_| panic!("Cannot index an array by \"{}\"", my));

        if let Some(subpath) = sub {
            self.get_mut(my)
                .map(|m: &mut Value| m.get_mut(subpath))
                .unwrap_or_default()
        } else {
            self.get_mut(my)
        }
    }

    fn dot_set<T>(&mut self, path: &str, value: T)
    where
        T: Serialize,
    {
        let (mut my, sub) = path_split(path);

        if my.is_empty() {
            panic!("Cannot index array by empty key");
        }

        let mut insert = false;
        let mut add = 0isize;

        if my.starts_with('<') {
            // "<n" means insert before n
            // "<" means prepend
            insert = true;
            my = &my[1..];
        } else if my.starts_with('>') {
            insert = true;
            my = &my[1..];
            if my.is_empty() {
                // ">" means append
                add = self.len() as isize;
            } else {
                // ">n" means insert after
                add = 1;
            }
        }

        let mut my = match my {
            // append
            "+" => self.len(),
            // prepend
            "-" => {
                insert = true;
                0
            }
            // empty (this happens only if the < or > was removed above)
            "" => 0,
            _ => my
                .parse()
                .unwrap_or_else(|_| panic!("Cannot index an array by \"{}\"", my)),
        };

        my = (my as isize + add) as usize;

        match my.cmp(&self.len()) {
            Ordering::Less => {
                if insert {
                    // insert
                    if let Some(subpath) = sub {
                        self.insert(my, new_by_path_root(subpath, value));
                    } else {
                        self.insert(my, serde_json::to_value(value).expect("Serialize error"));
                    }
                } else {
                    // replace
                    if let Some(subpath) = sub {
                        self[my].dot_set(subpath, value);
                    } else {
                        self[my] = serde_json::to_value(value).expect("Serialize error");
                    }
                }
            }
            Ordering::Equal => {
                if let Some(subpath) = sub {
                    self.push(new_by_path_root(subpath, value))
                } else {
                    self.push(serde_json::to_value(value).expect("Serialize error"))
                }
            }
            Ordering::Greater => {
                panic!("Index out of bounds.");
            }
        }
    }

    fn dot_replace<T, U>(&mut self, path: &str, value: T) -> Option<U>
    where
        T: Serialize,
        U: DeserializeOwned,
    {
        let (my, sub) = path_split(path);
        let index = my
            .parse::<usize>()
            .unwrap_or_else(|_| panic!("Cannot index an array by \"{}\"", my));

        if let Some(subpath) = sub {
            if index < self.len() {
                let a_mut: &mut Value = self.get_mut(index).unwrap();
                a_mut.dot_replace(subpath, value)
            } else {
                // use the append implementation & validations from dot_set
                self.dot_set(path, value);
                None
            }
        } else {
            // No subpath
            if index < self.len() {
                let other = serde_json::to_value(value).expect("Serialize error");
                let old = mem::replace(&mut self[index], other);
                Some(serde_json::from_value(old).expect("Deserialize error"))
            } else {
                // use the append implementation & validations from dot_set
                self.dot_set(my, value);
                None
            }
        }
    }

    fn dot_take<T>(&mut self, path: &str) -> Option<T>
    where
        T: DeserializeOwned,
    {
        let (my, sub) = path_split(path);
        let my = my
            .parse()
            .unwrap_or_else(|_| panic!("Cannot index an array by \"{}\"", my));

        if my >= self.len() {
            return None;
        }

        if let Some(subpath) = sub {
            let value: &mut Value = &mut self[my];
            value.dot_take(subpath)
        } else {
            // bounds are checked above
            serde_json::from_value(self.remove(my)).expect("Deserialize error")
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::DotPaths;
    use serde_json::json;
    use serde_json::Value;

    #[test]
    fn get_scalar_with_empty_path() {
        let value = Value::String("Hello".to_string());
        assert_eq!(Some("Hello".to_string()), value.dot_get(""));
    }

    #[test]
    #[should_panic]
    fn cant_get_scalar_with_path() {
        let value = Value::String("Hello".to_string());
        let _ = value.dot_get::<Value>("1.2.3");
    }

    #[test]
    fn set_null() {
        let mut item = Value::Null;
        item.dot_set("", "foo");
        assert_eq!(Value::String("foo".into()), item);
    }

    #[test]
    fn replace_null() {
        let mut item = Value::Null;
        assert_eq!(None, item.dot_replace::<_, Value>("", "foo"));
        assert_eq!(Value::String("foo".into()), item);
    }

    #[test]
    fn take_null() {
        let mut item = Value::Null;
        assert_eq!(None, item.dot_take::<Value>(""));
        assert_eq!(Value::Null, item);

        let mut item = Value::Bool(true);
        assert_eq!(Some(true), item.dot_take::<bool>(""));
        assert_eq!(Value::Null, item);
    }

    #[test]
    fn set_vec() {
        let mut vec = Value::Array(vec![]);
        vec.dot_set("0", "first");
        vec.dot_set("0", "second"); // this replaces it
        vec.dot_set("1", "third");
        vec.dot_set("+", "append");
        vec.dot_set(">", "append2");
        vec.dot_set("-", "prepend");
        vec.dot_set("<", "prepend2");
        vec.dot_set("<0", "prepend3");
        vec.dot_set(">1", "insert after 1");
        vec.dot_set(">0", "after0");
        vec.dot_set("<2", "before2");
        assert_eq!(
            json!([
                "prepend3",
                "after0",
                "before2",
                "prepend2",
                "insert after 1",
                "prepend",
                "second",
                "third",
                "append",
                "append2"
            ]),
            vec
        );
    }

    #[test]
    #[should_panic]
    fn set_vec_panic_bad_index() {
        let mut vec = Value::Array(vec![]);
        vec.dot_set("1", "first");
    }

    #[test]
    #[should_panic]
    fn set_vec_panic_index_not_numeric() {
        let mut vec = Value::Array(vec![]);
        vec.dot_set("abc", "first");
    }

    #[test]
    fn set_vec_spawn() {
        let mut vec = Value::Array(vec![]);

        vec.dot_set("0.0.0", "first");
        vec.dot_set("+", "append");
        vec.dot_set("<1", "in between");
        assert_eq!(json!([[["first"]], "in between", "append"]), vec);

        vec.dot_set("0.0.+", "second");
        assert_eq!(json!([[["first", "second"]], "in between", "append"]), vec);

        vec.dot_set("0.+", "mmm");
        assert_eq!(
            json!([[["first", "second"], "mmm"], "in between", "append"]),
            vec
        );

        vec.dot_set("0.+.0", "xyz");
        assert_eq!(
            json!([
                [["first", "second"], "mmm", ["xyz"]],
                "in between",
                "append"
            ]),
            vec
        );

        // append and prepend can also spawn a new array
        let mut vec = Value::Array(vec![]);
        vec.dot_set(">.>.>", "first");
        assert_eq!(json!([[["first"]]]), vec);
        vec.dot_set(">.<.>", "second");
        assert_eq!(json!([[["first"]], [["second"]]]), vec);
    }

    #[test]
    fn get_vec() {
        let vec = json!([
            [["first", "second"], "mmm", ["xyz"]],
            "in between",
            "append"
        ]);
        assert_eq!(Some("first".to_string()), vec.dot_get("0.0.0"));
        assert_eq!(Some("second".to_string()), vec.dot_get("0.0.1"));

        // this one doesn't exist
        assert_eq!(None, vec.dot_get::<String>("0.0.3"));

        // get last
        assert_eq!(Some(json!(["xyz"])), vec.dot_get("0.>"));

        // retrieve a Value
        assert_eq!(
            Some(json!([["first", "second"], "mmm", ["xyz"]])),
            vec.dot_get("0")
        );
        assert_eq!(Some(json!(["first", "second"])), vec.dot_get("0.0"));
    }

    #[test]
    #[should_panic]
    fn get_vec_panic_index_scalar() {
        let vec = json!([
            [["first", "second"], "mmm", ["xyz"]],
            "in between",
            "append"
        ]);
        let _ = vec.dot_get::<Value>("0.0.1.4");
    }

    #[test]
    fn take_from_vec() {
        let mut vec = json!(["a", "b", "c"]);

        // test Take
        assert_eq!(Some("b".to_string()), vec.dot_take("1"));
        assert_eq!(None, vec.dot_take::<Value>("4"));
        assert_eq!(json!(["a", "c"]), vec);

        let mut vec = json!([[["a"], "b"], "c"]);
        assert_eq!(Some("a".to_string()), vec.dot_take("0.0.0"));
        assert_eq!(json!([[[], "b"], "c"]), vec); // empty vec is left in place
    }

    #[test]
    fn remove_from_vec() {
        let mut vec = json!(["a", "b", "c"]);

        assert_eq!(true, vec.dot_remove("1"));
        assert_eq!(false, vec.dot_remove("4"));
        assert_eq!(json!(["a", "c"]), vec);

        let mut vec = json!([[["a"], "b"], "c"]);
        assert_eq!(true, vec.dot_remove("0.0.0"));
        assert_eq!(false, vec.dot_remove("0.0.0"));
        assert_eq!(json!([[[], "b"], "c"]), vec); // empty vec is left in place
    }

    #[test]
    fn replace_in_vec() {
        let mut vec = json!(["a", "b", "c"]);

        assert_eq!(Some("b".to_string()), vec.dot_replace("1", "BBB"));

        let mut vec = json!([[["a"], "b"], "c"]);
        assert_eq!(Some("a".to_string()), vec.dot_replace("0.0.0", "AAA"));
        assert_eq!(json!([[["AAA"], "b"], "c"]), vec);
    }

    #[test]
    fn set_map() {
        let mut vec = json!({});
        vec.dot_set("foo", "bar");
        assert_eq!(json!({"foo": "bar"}), vec);

        let mut vec = json!({});
        vec.dot_set("foo.bar.baz", "binx");
        assert_eq!(json!({"foo": {"bar": {"baz": "binx"}}}), vec);

        vec.dot_set("foo.bar.abc.0", "aaa");
        assert_eq!(json!({"foo": {"bar": {"baz": "binx","abc": ["aaa"]}}}), vec);
    }

    #[test]
    #[should_panic]
    fn set_map_panic_bad_index() {
        let mut vec = json!({});
        vec.dot_set("0", "first");
    }

    #[test]
    fn get_map() {
        let vec = json!({"one": "two"});
        assert_eq!(Some("two".to_string()), vec.dot_get("one"));

        let vec = json!({"one": {"two": "three"}});
        assert_eq!(Some("three".to_string()), vec.dot_get("one.two"));

        let vec = json!({"one": "two"});
        assert_eq!(None, vec.dot_get::<Value>("xxx"));
    }

    #[test]
    fn remove_from_map() {
        let mut vec = json!({"one": "two", "x": "y"});
        assert_eq!(true, vec.dot_remove("one"));
        assert_eq!(json!({"x": "y"}), vec);
    }

    #[test]
    fn take_from_map() {
        let mut vec = json!({"one": "two", "x": "y"});
        assert_eq!(Some("two".to_string()), vec.dot_take("one"));
        assert_eq!(json!({"x": "y"}), vec);
    }

    #[test]
    fn replace_in_map() {
        let mut vec = json!({"one": "two", "x": "y"});
        assert_eq!(Some("two".to_string()), vec.dot_replace("one", "fff"));
        assert_eq!(json!({"one": "fff", "x": "y"}), vec);

        // replace value for string
        let mut vec = json!({"one": "two", "x": {"bbb": "y"}});
        assert_eq!(Some("y".to_string()), vec.dot_replace("x.bbb", "mm"));
        assert_eq!(
            Some(json!({"bbb": "mm"})),
            vec.dot_replace("x", "betelgeuze")
        );
        assert_eq!(json!({"one": "two", "x": "betelgeuze"}), vec);

        // nested replace
        let mut vec = json!({"one": "two", "x": {"bbb": ["y"]}});
        assert_eq!(
            Some("y".to_string()),
            vec.dot_replace("x.bbb.0", "betelgeuze")
        );
        assert_eq!(json!({"one": "two", "x": {"bbb": ["betelgeuze"]}}), vec);
    }
}
