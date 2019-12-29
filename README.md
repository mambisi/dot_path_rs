# json_dotpath

Access members of nested JSON arrays and objects using "dotted paths".

Consider this example JSON:

```json
{
  "fruit": [
    {"name": "lemon", "color":  "yellow"},
    {"name": "apple", "color":  "green"},
    {"name": "cherry", "color":  "red"}
  ]
}
```

The following can be used to access its parts:
- `obj.dot_get("fruit")` ... get the fruits array
- `obj.dot_get("fruit.0.name")` ... 0th fruit name, "lemon"
- `obj.dot_get("fruit.>.color")` ... last fruit's color, "red"

The JSON can also be manipulated:

- `obj.dot_take("fruit.1")` ... extract the "apple" object, removing it from the JSON
- `obj.dot_set("fruit.<1", json!({"name":"plum","color":"blue"})` ... insert before the 1st element, shifting the rest
- `obj.dot_set("fruit.>1", json!({"name":"plum","color":"blue"})` ... insert after the 1st element, shifting the rest
- `obj.dot_set("fruit.>.name", "tangerine")` ... set the last fruit's name
- `obj.dot_set("fruit.>", Value::Null)` ... append a JSON null
- `obj.dot_set("fruit.<", true)` ... prepend a JSON true
- `obj.dot_set("vegetables.onion.>", "aaa")` ... add `{"vegetables":{"onion":["aaa"]}}` to the object

Any serializable type or `serde_json::Value` can be stored to or retrieved from
the nested object (`Value::Object`, `Value::Array`, `Value::Null`).
 
Any value stored in the object can also be modified in place, without deserialization, 
by getting a mutable reference (`dot_get_mut(path)`).

This crate is useful for tasks such as working with dynamic JSON API payloads,
parsing config files, or building a polymorphic data store.

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

### Map Patterns

To avoid ambiguity, it's not allowed to use numeric keys (or keys starting with a number) 
as map keys. Map keys must start with an ASCII letter or underscore and must not contain a dot (`.`).

Examples:

- `abc`
- `_123`
- `key with spaces`

If a numeric key or a key nonconforming in other way must be used, prefix it with `#`. 
It will be taken literally as a string, excluding the prefix.

e.g. to get 456 from `{"foo":{"123":456}}`, use `foo.#123` instead of `foo.123`

### Array Patterns

Array keys must be numeric (integer), or one of the special patterns listed below.

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
