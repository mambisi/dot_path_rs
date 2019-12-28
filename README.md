# json_dotpath

Access members of nested JSON arrays and objects using "dotted paths".

The `DotPaths` trait is implemented for `serde_json::Value`, 
`serde_json::Map<String, serde_json::Value>`, and  `Vec<serde_json::Value>`.

Any serializable type or `serde_json::Value` can be stored to or retrieved from
the nested object. Any value stored in the object can also be modified in place 
by getting a mutable reference.

This crate is useful for tasks such as working with dynamic JSON API payloads,
parsing config files, or polymorphic data store.

## Supported Operations

### Object and Array
- Set (dropping the original value, if any)
- Remove (remove and drop a value)
- Take (remove a value and deserialize it)
- Replace (take and set)
- Get (find & deserialize)
- Get a mutable reference to a Value

### Array
Array is an ordered sequence backed by a Vec. It has these additional operations:

- Prepend
- Append
- Insert, shifting the following elements
- Get the last element

### Null
JSON null can become an array or object by setting it's members (even nested), as if it was an array or object.
It becomes an array or object of the appropriate type based on the root key.

## Dotted Path Syntax

Array keys must be numeric (integer), or one of the special patterns listed below.

To avoid ambiguity, it's not allowed to use numeric keys (or keys starting with a number) 
as map keys. Map keys must start with an ASCII letter or underscore and must not contain a dot (`.`).

### Array Index Patterns

- `-` ... prepend
- `<` ... prepend (or get first)
- `+` ... append
- `>` ... append (or get last)
- `<n`, e.g. `<5` ... insert before the n-th element
- `>n`, e.g. `>5` ... insert after the n-th element

### Path Examples

- Empty path ... access the root element
- `5` ... get the element `"five"` from `[0,1,2,3,4,"five"]`
- `a.b.c` ... get `1` from `{ "a": { "b": { "c": 1 } } }`
- `a.0.x` ... get `1` from `{ "a": [ { "x": 1 } ] }`

It's possible to create nested arrays or objects by setting a non-existent path,
provided the key syntax rules are maintained. 

See unit tests for more examples.
