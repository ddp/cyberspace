# uri-generic - RFC 3986 URI Parser

**Source:** http://wiki.call-cc.org/eggref/5/uri-generic

**License:** BSD 3-Clause (2008-2021)

**Dependencies:** matchable, srfi-1, srfi-14

## Overview

The uri-generic library is a CHICKEN Scheme egg for parsing and manipulating Uniform Resource Identifiers according to RFC 3986. It uses combinator parsing and character classes rather than regex patterns.

## Key Design Philosophy

This library functions as a foundational tool for creating scheme-specific URI parsers.

**Important:** "Encoding and decoding of percent-encoded characters is not done automatically" since specific URI scheme implementations should handle this.

**Recommendation:** For practical use with common schemes (HTTP, FTP, etc.), the **uri-common** egg is recommended as it provides automatic percent-encoding/decoding and scheme-specific handling.

## Core API

### Constructors & Predicates

#### `uri-reference`

```scheme
(uri-reference STRING)
```

Parses strings as URI references or relative references.

**Example:**

```scheme
(uri-reference "http://example.com/path")
(uri-reference "/relative/path")
(uri-reference "//example.com/path")
```

#### `absolute-uri`

```scheme
(absolute-uri STRING)
```

Parses absolute URIs without fragments. Raises error if scheme is missing.

**Example:**

```scheme
(absolute-uri "http://example.com/")
; OK

(absolute-uri "/relative")
; Error: no scheme
```

#### `make-uri`

```scheme
(make-uri #:scheme SCHEME #:host HOST #:path PATH ...)
```

Constructs URIs from components.

**Example:**

```scheme
(make-uri
  #:scheme "http"
  #:host "example.com"
  #:path '("path" "to" "file"))
```

#### Type Checking Predicates

```scheme
(uri? OBJ)                               ; Has URI structure
(absolute-uri? URI)                      ; No fragment present
(relative-ref? URI)                      ; No scheme component
```

### Accessors

Functions retrieve individual components:

```scheme
(uri-scheme URI)                         ; => "http" or #f
(uri-host URI)                           ; => "example.com" or #f
(uri-path URI)                           ; => ("path" "to" "file")
(uri-query URI)                          ; => "key=value" or #f
(uri-fragment URI)                       ; => "section" or #f
(uri-port URI)                           ; => 8080 or #f
(uri-username URI)                       ; => "user" or #f
(uri-password URI)                       ; => "pass" or #f
```

**Note:** Missing components return `#f`, except `uri-path` which returns a list.

### String Operations

#### `uri->string`

```scheme
(uri->string URI)
```

Reconstructs URIs as strings.

**Example:**

```scheme
(define u (uri-reference "http://example.com/path?query#fragment"))
(uri->string u)
; => "http://example.com/path?query#fragment"
```

#### `uri->list`

```scheme
(uri->list URI)
```

Returns structured list representation.

**Example:**

```scheme
(uri->list (uri-reference "http://example.com/path"))
; => (scheme authority path query fragment)
```

#### Percent Encoding/Decoding

```scheme
(uri-encode-string STRING [CHAR-SET])
(uri-decode-string STRING)
```

**Examples:**

```scheme
(uri-encode-string "hello world")
; => "hello%20world"

(uri-decode-string "hello%20world")
; => "hello world"
```

### Resolution

#### `uri-relative-to`

```scheme
(uri-relative-to RELATIVE-URI BASE-URI)
```

Resolves relative references against base URIs per RFC 3986.

**Example:**

```scheme
(define base (uri-reference "http://example.com/a/b/c"))
(uri-relative-to (uri-reference "../d") base)
; => URI for "http://example.com/a/d"
```

#### `uri-relative-from`

```scheme
(uri-relative-from TARGET-URI BASE-URI)
```

Constructs relative URI from target to base.

**Example:**

```scheme
(define base (uri-reference "http://example.com/a/b/c"))
(define target (uri-reference "http://example.com/a/d/e"))
(uri-relative-from target base)
; => URI for "../d/e"
```

### Normalization

#### `uri-normalize-case`

```scheme
(uri-normalize-case URI)
```

Normalizes scheme and host to lowercase per RFC 3986.

**Example:**

```scheme
(uri-normalize-case (uri-reference "HTTP://EXAMPLE.COM/Path"))
; => "http://example.com/Path" (path case preserved)
```

#### `uri-normalize-path-segments`

```scheme
(uri-normalize-path-segments URI)
```

Resolves `.` and `..` path segments per RFC 3986.

**Example:**

```scheme
(uri-normalize-path-segments
  (uri-reference "http://example.com/a/b/../c/./d"))
; => "http://example.com/a/c/d"
```

## Usage Examples

### Basic Parsing

```scheme
(import uri-generic)

(define url (uri-reference "http://user:pass@example.com:8080/path?query#frag"))

(uri-scheme url)        ; => "http"
(uri-username url)      ; => "user"
(uri-password url)      ; => "pass"  (NOT automatically decoded)
(uri-host url)          ; => "example.com"
(uri-port url)          ; => 8080
(uri-path url)          ; => ("" "path")
(uri-query url)         ; => "query"  (NOT automatically decoded)
(uri-fragment url)      ; => "frag"
```

### Building URIs

```scheme
(import uri-generic)

(define uri
  (make-uri
    #:scheme "https"
    #:host "api.example.com"
    #:path '("" "v1" "users")
    #:query "format=json"))

(uri->string uri)
; => "https://api.example.com/v1/users?format=json"
```

### Relative Resolution

```scheme
(import uri-generic)

(define base (uri-reference "http://example.com/docs/guide/intro.html"))

;; Resolve relative paths
(uri->string (uri-relative-to (uri-reference "../api/ref.html") base))
; => "http://example.com/docs/api/ref.html"

(uri->string (uri-relative-to (uri-reference "?page=2") base))
; => "http://example.com/docs/guide/intro.html?page=2"
```

### Path Normalization

```scheme
(import uri-generic)

(define messy (uri-reference "http://example.com/a/./b/../c/d"))
(define clean (uri-normalize-path-segments messy))

(uri->string clean)
; => "http://example.com/a/c/d"
```

### Manual Percent Encoding

```scheme
(import uri-generic)

;; Encode query parameter
(define query
  (string-append
    "search="
    (uri-encode-string "hello world & stuff")))

(define uri
  (make-uri
    #:scheme "http"
    #:host "example.com"
    #:path '("" "search")
    #:query query))

(uri->string uri)
; => "http://example.com/search?search=hello%20world%20%26%20stuff"
```

## Comparison with uri-common

| Feature | uri-generic | uri-common |
|---------|-------------|------------|
| **Percent encoding** | Manual | Automatic |
| **Query parsing** | String only | Parsed to alist |
| **Path format** | List of strings | Special path format with `/` |
| **Use case** | Low-level parsing | Common HTTP/FTP/etc URIs |
| **Complexity** | Simpler, generic | Scheme-aware |

**When to use uri-generic:**
- Building custom URI schemes
- Need fine control over encoding
- Working with non-standard URIs

**When to use uri-common:**
- Working with HTTP, HTTPS, FTP
- Want automatic encoding/decoding
- Need query parameter parsing

## Installation

```bash
chicken-install uri-generic
```

## See Also

- uri-common (higher-level common scheme parser)
- RFC 3986 (URI specification)
- intarweb (HTTP utilities)
