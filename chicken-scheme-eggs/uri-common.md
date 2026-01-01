# uri-common - URI Parsing for Common Schemes

**Source:** http://wiki.call-cc.org/eggref/5/uri-common

**License:** BSD 2-Clause

**Author:** Peter Bex (2008-2018)

**Dependencies:** srfi-1, srfi-13, srfi-14, defstruct, matchable, uri-generic

## Overview

The uri-common library is a CHICKEN Scheme egg providing "simple and easy-to-use parsing and manipulation procedures for URIs using common schemes" (HTTP, HTTPS, FTP, etc.).

## Key Characteristics

Common schemes follow these rules:
- Empty paths after hostnames equal root paths
- All components are fully URI-decoded
- Query arguments use application/x-www-form-urlencoded format
- Ports auto-determine based on known schemes

## Core API

### Constructors & Predicates

#### `uri-reference`

```scheme
(uri-reference STRING)
```

Parses URIs or relative references per RFC 3986.

**Examples:**

```scheme
(uri-reference "http://example.com/path")
(uri-reference "/relative/path")
(uri-reference "//example.com/path")
```

#### `absolute-uri`

```scheme
(absolute-uri STRING)
```

Parses non-fragment URIs; raises errors if scheme missing.

**Example:**

```scheme
(absolute-uri "http://example.com/")
```

#### `make-uri`

```scheme
(make-uri #:scheme SCHEME #:host HOST #:path PATH ...)
```

Constructs URIs from component keyword arguments.

**Example:**

```scheme
(make-uri
  #:scheme "http"
  #:host "example.com"
  #:path '(/ "api" "users")
  #:query '((page . "1") (limit . "10")))
```

### Accessors

Retrieve individual components:

```scheme
(uri-scheme URI)                         ; => "http"
(uri-host URI)                           ; => "example.com"
(uri-port URI)                           ; => 80 or #f
(uri-path URI)                           ; => '(/ "path" "to" "resource")
(uri-query URI)                          ; => '((key . "value") ...)
(uri-fragment URI)                       ; => "section" or #f
(uri-username URI)                       ; => "user" or #f
(uri-password URI)                       ; => "pass" or #f
```

**Notes:**
- Missing components return `#f`
- `uri-query` and `uri-path` always return lists (empty if missing)

### Updating

#### `update-uri`

```scheme
(update-uri URI #:key VALUE ...)
```

Functionally modifies URI components.

**Example:**

```scheme
(define base (uri-reference "http://example.com/old"))
(define updated (update-uri base
                  #:path '(/ "new")
                  #:query '((id . "123"))))
; => "http://example.com/new?id=123"
```

### URI Classification Predicates

```scheme
(uri-reference? OBJ)                     ; Most general type
(absolute-uri? URI)                      ; No fragment present
(uri? OBJ)                               ; Includes scheme component
(relative-ref? URI)                      ; No scheme component
(uri-path-absolute? URI)                 ; Path starts with /
(uri-path-relative? URI)                 ; Path doesn't start with /
(uri-default-port? URI)                  ; Port matches scheme default
```

### Reference Resolution

#### `uri-relative-to`

```scheme
(uri-relative-to URI BASE-URI)
```

Resolves relative references against base URIs.

**Example:**

```scheme
(define base (uri-reference "http://example.com/path/to/page"))
(uri-relative-to (uri-reference "../other") base)
; => "http://example.com/path/other"
```

#### `uri-relative-from`

```scheme
(uri-relative-from URI BASE-URI)
```

Constructs relative URIs between locations.

**Example:**

```scheme
(define base (uri-reference "http://example.com/a/b/c"))
(define target (uri-reference "http://example.com/a/d/e"))
(uri-relative-from target base)
; => "../d/e"
```

### Query Encoding/Decoding

#### `form-urlencode`

```scheme
(form-urlencode ALIST [SEPARATOR])
```

Converts association list to URL-encoded query string.

**Example:**

```scheme
(form-urlencode '((name . "Alice Smith") (age . "30")))
; => "name=Alice%20Smith&age=30"

(form-urlencode '((a . "1") (b . "2")) ";")
; => "a=1;b=2"
```

#### `form-urldecode`

```scheme
(form-urldecode STRING [SEPARATOR])
```

Parses URL-encoded query string into association list.

**Example:**

```scheme
(form-urldecode "name=Alice%20Smith&age=30")
; => ((name . "Alice Smith") (age . "30"))
```

#### `form-urlencoded-separator`

```scheme
(form-urlencoded-separator [SEPARATORS])
```

Parameter controlling separator behavior (default: ";&").

**Example:**

```scheme
(form-urlencoded-separator ";")
```

### String Encoding/Decoding

#### `uri-encode-string`

```scheme
(uri-encode-string STRING [CHAR-SET])
```

Percent-encodes strings.

**Example:**

```scheme
(uri-encode-string "hello world")
; => "hello%20world"

(uri-encode-string "a/b/c" char-set:uri-unreserved)
; => "a%2Fb%2Fc"
```

#### `uri-decode-string`

```scheme
(uri-decode-string STRING)
```

Reverses percent-encoding.

**Example:**

```scheme
(uri-decode-string "hello%20world")
; => "hello world"
```

### Normalization

#### `uri-normalize-case`

```scheme
(uri-normalize-case URI)
```

RFC 3986 case normalization (scheme and host to lowercase).

#### `uri-normalize-path-segments`

```scheme
(uri-normalize-path-segments URI)
```

RFC 3986 path segment normalization (resolve . and ..).

**Example:**

```scheme
(uri-normalize-path-segments
  (uri-reference "http://example.com/a/b/../c/./d"))
; => "http://example.com/a/c/d"
```

### Conversion Functions

```scheme
(uri->uri-generic URI)                   ; Convert to uri-generic format
(uri-generic->uri URI)                   ; Convert from uri-generic format
(uri->string URI [HIDE-USERINFO])        ; Reconstruct URI string
(uri->list URI)                          ; Three-element list structure
```

**Example:**

```scheme
(uri->string (uri-reference "http://user:pass@example.com/"))
; => "http://user:pass@example.com/"

(uri->string (uri-reference "http://user:pass@example.com/") #t)
; => "http://example.com/"  (userinfo hidden)
```

### Character Sets

Exported constants for URI component validation:

```scheme
char-set:gen-delims
char-set:sub-delims
char-set:uri-reserved
char-set:uri-unreserved
```

## Complete Examples

### Parse and Extract Components

```scheme
(import uri-common)

(define url (uri-reference "http://user:pass@example.com:8080/path/to/page?id=123&page=2#section"))

(uri-scheme url)        ; => "http"
(uri-username url)      ; => "user"
(uri-password url)      ; => "pass"
(uri-host url)          ; => "example.com"
(uri-port url)          ; => 8080
(uri-path url)          ; => (/ "path" "to" "page")
(uri-query url)         ; => ((id . "123") (page . "2"))
(uri-fragment url)      ; => "section"
```

### Build URI from Components

```scheme
(import uri-common)

(define api-url
  (make-uri
    #:scheme "https"
    #:host "api.example.com"
    #:path '(/ "v1" "users" "123")
    #:query '((format . "json") (include . "profile"))))

(uri->string api-url)
; => "https://api.example.com/v1/users/123?format=json&include=profile"
```

### Resolve Relative URLs

```scheme
(import uri-common)

(define base (uri-reference "http://example.com/docs/guide/intro.html"))

(uri->string (uri-relative-to (uri-reference "../api/ref.html") base))
; => "http://example.com/docs/api/ref.html"

(uri->string (uri-relative-to (uri-reference "/blog/post") base))
; => "http://example.com/blog/post"

(uri->string (uri-relative-to (uri-reference "?page=2") base))
; => "http://example.com/docs/guide/intro.html?page=2"
```

### Update URI Components

```scheme
(import uri-common)

(define url (uri-reference "http://example.com/old?page=1"))

(define new-url
  (update-uri url
    #:path '(/ "new")
    #:query '((page . "2") (sort . "date"))))

(uri->string new-url)
; => "http://example.com/new?page=2&sort=date"
```

## Installation

```bash
chicken-install uri-common
```

## See Also

- uri-generic (low-level RFC 3986 parser)
- intarweb (HTTP request/response handling)
- http-client (HTTP client library)
