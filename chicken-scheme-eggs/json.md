# json - JSON Serialization and Parsing

**Source:** http://wiki.call-cc.org/eggref/5/json

**License:** MIT

**Author:** Tony Garnock-Jones

**Dependencies:** packrat

**Version:** 1.7 (CHICKEN 6 compatible)

## Overview

The json egg is a CHICKEN Scheme extension that handles JSON data serialization and deserialization. It provides straightforward procedures for converting between Scheme objects and JSON format.

## Core API

### `json-write`

```scheme
(json-write object [port])
```

Serializes Scheme data to JSON format.

**Parameters:**
- `object` - Scheme data to serialize
- `port` - Output port (optional, defaults to current output port)

**Type Mapping (Scheme → JSON):**

| Scheme Type | JSON Type |
|-------------|-----------|
| Hash-table | Object |
| Vector of symbol-data pairs | Object |
| List | Array |
| Number | Number |
| Void | null |
| String | String |
| Symbol | String |

**Examples:**

```scheme
(import json)

;; Simple values
(json-write 42)                           ; 42
(json-write "hello")                      ; "hello"
(json-write '(1 2 3))                     ; [1,2,3]

;; Objects using vectors
(json-write '#((name . "Alice") (age . 30)))
; {"name":"Alice","age":30}

;; Using hash-tables
(use srfi-69)
(define ht (make-hash-table))
(hash-table-set! ht "name" "Bob")
(hash-table-set! ht "score" 95)
(json-write ht)
; {"name":"Bob","score":95}

;; Nested structures
(json-write '(#((type . "person") (name . "Charlie"))
              #((type . "person") (name . "Diana"))))
; [{"type":"person","name":"Charlie"},{"type":"person","name":"Diana"}]
```

### `json-read`

```scheme
(json-read [port])
```

Parses JSON data from an input source.

**Parameters:**
- `port` - Input port (optional, defaults to current input port)

**Type Mapping (JSON → Scheme):**

| JSON Type | Scheme Type |
|-----------|-------------|
| Object | Vector of (string . value) pairs |
| Array | List |
| Number | Number |
| null | Void |
| String | String |
| true/false | Boolean |

**Important Note:** "json-read does not produce alists, as the result are vectors and not lists, and keys are strings and not symbols."

**Examples:**

```scheme
;; Parse from string (using string ports)
(with-input-from-string "{\"name\":\"Alice\",\"age\":30}"
  json-read)
; => #((\"name\" . \"Alice\") (\"age\" . 30))

;; Parse array
(with-input-from-string "[1,2,3,4,5]"
  json-read)
; => (1 2 3 4 5)

;; Parse nested structure
(with-input-from-string "{\"users\":[\"Alice\",\"Bob\"]}"
  json-read)
; => #((\"users\" . (\"Alice\" \"Bob\")))

;; Parse from file
(with-input-from-file "data.json"
  json-read)
```

## Working with JSON Objects

Since JSON objects are represented as vectors of pairs with string keys, you'll need to search through them:

```scheme
(define (json-ref json-obj key)
  (let ((pair (vector-find (lambda (p) (string=? (car p) key)) json-obj)))
    (and pair (cdr pair))))

(define obj (with-input-from-string "{\"name\":\"Alice\",\"age\":30}" json-read))
(json-ref obj "name")                     ; => "Alice"
(json-ref obj "age")                      ; => 30
```

Or convert to hash-table:

```scheme
(use srfi-69)

(define (json-obj->hash-table vec)
  (let ((ht (make-hash-table)))
    (vector-for-each
      (lambda (pair)
        (hash-table-set! ht (car pair) (cdr pair)))
      vec)
    ht))
```

## Complete Example

```scheme
(import json)
(import srfi-69)  ; hash-tables

;; Create JSON data
(define person-data (make-hash-table))
(hash-table-set! person-data "name" "Alice")
(hash-table-set! person-data "age" 30)
(hash-table-set! person-data "hobbies" '("reading" "coding"))

;; Write to string
(define json-string
  (with-output-to-string
    (lambda () (json-write person-data))))

(display json-string)
; {"name":"Alice","age":30,"hobbies":["reading","coding"]}

;; Read back
(define parsed
  (with-input-from-string json-string json-read))

;; Access data
(vector-ref parsed 0)                     ; => ("name" . "Alice")
```

## Installation

```bash
chicken-install json
```

## Related Eggs

- **json-abnf** - Alternative JSON implementation
- **medea** - Another JSON parser
- **packrat** - PEG parser (dependency)

## See Also

- RFC 8259 (JSON specification)
- SRFI-69 (hash-tables)
