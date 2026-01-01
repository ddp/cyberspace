# chicken-doc - Documentation Explorer

**Source:** http://wiki.call-cc.org/eggref/5/chicken-doc

**License:** BSD

**Author:** Jim Ursetto

**Repository:** https://github.com/ursetto/chicken-doc

## Overview

chicken-doc is a tool for exploring CHICKEN documentation. It provides command-line and REPL access to CHICKEN Scheme documentation, plus an API for programmatic access.

## Key Features

**Documentation Access:**
- Command-line interface for querying documentation
- REPL integration via `csi` commands
- API for embedding in Scheme programs
- Tree-structured documentation organization

## Configuration

**Repository Location:**

The tool locates repositories via the `CHICKEN_DOC_REPOSITORY` environment variable, defaulting to `(chicken-home)/chicken-doc/`.

**Environment Variables:**

- `CHICKEN_DOC_REPOSITORY` - Documentation repository location
- `CHICKEN_DOC_PAGER` or `PAGER` - Pager program (defaults: `less` on UNIX, `more` on Windows)
- `CHICKEN_DOC_WRAP` - Text wrapping column width (default: 76)
- `CHICKEN_DOC_COLORS` - Colorization: "auto", "always", or "never" for ANSI formatting

## Command-Line Usage

Primary syntax patterns:

```bash
chicken-doc -s path        # Display signature
chicken-doc -c path        # Show table of contents
chicken-doc -i path        # Display documentation
chicken-doc -f node        # Find all matching paths
chicken-doc -m regex       # Match identifiers via regular expressions
```

Without options, the tool intelligently infers user intent based on input.

**Examples:**

```bash
chicken-doc map
chicken-doc -s srfi-1 map
chicken-doc -c srfi-1
chicken-doc -f "delete"
chicken-doc -m "^delete"
```

## REPL Commands

Available after loading the library:

```scheme
(import chicken-doc)

,doc node          ; Show documentation
,toc node          ; Display table of contents
,wtf regex         ; Search using regular expressions
```

**Examples:**

```scheme
,doc map
,doc srfi-1 map
,toc srfi-1
,wtf "delete.*"
```

## API Reference

### Repository Management

```scheme
(verify-repository [repository])
(open-repository [repository])
(close-repository repository)
(current-repository)  ; parameter
```

### Node Lookup

```scheme
(lookup-node path [repository])
(match-nodes pattern [repository])
(match-node-paths/re regex [repository])
(match-ids/prefix prefix [repository])
(match-paths/prefix prefix [repository])
```

### Node Information

The `chicken-doc-node` record provides access to:
- Signatures
- Types
- Paths
- Children
- Content (via SXML)

### Output Procedures

```scheme
(describe node)                    ; Format and display node text
(describe-contents node)           ; Show child nodes
(describe-signatures node)         ; Display matching signatures
(doc-dwim string [repository])     ; "Do-what-I-mean" intelligent lookup
```

## Documentation Structure

Documentation follows a hierarchical structure where units and eggs occupy top-level nodes, with identifiers as children. Core bindings in the chicken module are divided by manual page sections.

## Installation

```bash
chicken-install chicken-doc
```

## See Also

- apropos (symbol search)
- chicken-doc-admin (documentation management)
