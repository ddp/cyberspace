# Cyberspace Library Directory System

**"Peace for All Mankind" - Finding knowledge should be delightful**

A comprehensive cataloging and search system for the cyberspace research library, implemented in Chicken Scheme.

## Philosophy

This directory system embodies the cyberspace philosophy:
- **Knowledge wants to be found** - Intelligent search that understands what you need
- **No barriers** - Natural language queries, fuzzy matching, helpful suggestions
- **Delight** - Beautiful output, clear guidance, joyful exploration
- **Precision** - Hone in on exactly what you need, no more, no less

## Features

### 🔍 Intelligent Search
- **Natural language queries**: "papers by Lampson", "about SPKI", "from 1971"
- **Fuzzy matching**: Partial names work ("Lamp" finds Lampson, Lamport)
- **Cross-referencing**: Find related papers by author, topic, or collection
- **Smart suggestions**: "Did you mean...?" when queries don't match

### 📚 Comprehensive Indexing
- **Author index**: Alphabetical listing of all researchers
- **Topic index**: Sorted by frequency and relevance
- **Chronological index**: Papers by publication year
- **Collection index**: Browse themed collections (cryptographers, lamport-papers, etc.)

### 💎 Beautiful Display
- **Formatted output**: Unicode box drawing, emojis, clear typography
- **Contextual information**: Authors, years, collections, file paths
- **Summary statistics**: Collection sizes, document counts, year ranges
- **Progressive disclosure**: Brief lists, detailed views on demand

### 🔧 Export Capabilities
- **S-expressions**: Native Scheme format for programmatic use
- **HTML**: Web-browsable catalogs with styling
- **Markdown**: Documentation-friendly format
- **JSON**: (planned) For web APIs and integration

## Architecture

### Module Structure

```
directory.scm           - Core library and data structures
directory-parser.scm    - INDEX.md markdown parser
directory-repl.scm      - Interactive REPL interface
directory-example.scm   - Usage examples
```

### Data Model

**Document Record**:
- `title` - Paper title
- `authors` - List of author names
- `year` - Publication year
- `file-path` - Path to PDF
- `collection` - Collection name
- `size` - File size
- `topics` - Keywords/topics
- `citations` - Formatted citation
- `notes` - Additional metadata

**Collection Record**:
- `name` - Collection identifier
- `path` - Filesystem path
- `documents` - List of documents
- `index-file` - Path to INDEX.md
- `description` - Overview text
- `date-collected` - Collection date

**Library Record**:
- `root-path` - Library root directory
- `collections` - List of collections
- `documents` - All documents (flattened)
- `author-index` - Hash table: author → documents
- `topic-index` - Hash table: topic → documents
- `year-index` - Hash table: year → documents
- `collection-index` - Hash table: collection → collection

### Search Algorithm

The query parser implements a natural language understanding system:

1. **Intent detection**: Identify query type (author, topic, year, keyword)
2. **Entity extraction**: Pull out names, dates, keywords
3. **Fuzzy matching**: Handle partial matches and typos
4. **Result ranking**: Sort by relevance (exact matches first)
5. **Suggestion generation**: Offer alternatives when no results

## Usage

### Interactive REPL

The most delightful way to explore:

```scheme
(use directory)
(use directory-repl)

;; Launch the REPL
(directory-repl (load-library "~/cyberspace"))
```

Then query naturally:
```
📖 > papers by Lampson
📚 Found 5 documents:

 [1] Protection
     👤 Butler Lampson
     📅 1971  📁 lampson

 [2] The Digital Distributed System Security Architecture
     👤 M. Gasser, A. Goldstein, C. Kaufman, B. Lampson
     📅 1989  📁 lampson
...

📖 > about SPKI
📖 > from 1999
📖 > help
```

### Programmatic Use

For scripts and automation:

```scheme
(use directory)

;; Load the library
(define lib (load-library "~/cyberspace"))

;; Find papers by author
(define lampson-papers (find-by-author lib "Butler Lampson"))

;; Find papers by topic
(define spki-papers (find-by-topic lib "SPKI"))

;; Find papers from a year
(define papers-1971 (find-by-year lib 1971))

;; Search by keyword
(define auth-papers (search-documents lib "authentication"))

;; Generate indexes
(define authors (generate-author-index lib))
(define topics (generate-topic-index lib))
(define years (generate-chronological-index lib))

;; Find related papers
(define related (generate-cross-reference-index lib (car lampson-papers)))

;; Export to HTML
(export-to-html lib "catalog.html")
```

### Examples

Run the examples to see the system in action:

```bash
$ csi -s directory-example.scm

=== Example 1: Basic Library Usage ===
Library Statistics:
Collections: 18
Total Documents: 312
Unique Authors: 87
...
```

## Query Language

### Natural Language Patterns

| Query Pattern | Example | Finds |
|---------------|---------|-------|
| `papers by <author>` | papers by Rivest | All Rivest papers |
| `about <topic>` | about SPKI | Papers tagged SPKI |
| `from <year>` | from 1971 | Papers from 1971 |
| `in <year>` | in 1999 | Papers from 1999 |
| `collection:<name>` | collection:lampson | Lampson collection |
| `<keyword>` | authentication | Keyword search |

### Fuzzy Matching

Partial matches work:
- `Lamp` → finds Lampson, Lamport
- `auth` → finds authentication, authorization
- `spk` → finds SPKI, speaker, etc.

Case insensitive:
- `SPKI` = `spki` = `Spki`

### Commands

| Command | Description |
|---------|-------------|
| `help` | Show search tips |
| `stats` | Library statistics |
| `collections` | List all collections |
| `authors` | List all authors |
| `topics` | List all topics |
| `years` | List all years |
| `quit` | Exit REPL |

## INDEX.md Format

Collections are documented in INDEX.md files:

```markdown
# Collection Name - Description

**Collection Date**: 2026-01-03
**Location**: ~/cyberspace/library/collection-name/
**Total Size**: ~674 KB

## Overview

Description of the collection...

## Papers Collected

**filename.pdf** (44 KB)
- **Title**: "Paper Title"
- **Authors**: Author1, Author2
- **Published**: Venue, Year
- **Significance**: Why this paper matters
- **Source**: http://example.com/paper.pdf
```

The parser extracts:
- Collection metadata (date, size, description)
- Paper details (title, authors, publication info)
- Citations and source URLs
- File sizes and paths

## Installation

### Requirements

- Chicken Scheme 5.x
- SRFIs: 1 (lists), 13 (strings), 69 (hash tables)

### Setup

```bash
# Install Chicken Scheme (macOS)
brew install chicken

# Install required eggs
chicken-install srfi-1 srfi-13 srfi-69

# Clone or copy directory system files
cd ~/cyberspace
# Files: directory.scm, directory-parser.scm, directory-repl.scm
```

### Compilation

```bash
# Compile modules
csc -s directory.scm
csc -s directory-parser.scm

# Compile REPL
csc directory-repl.scm

# Run
./directory-repl
```

## Design Principles

### 1. **Helpfulness First**
- Clear error messages
- Helpful suggestions
- Natural language understanding
- Progressive disclosure of complexity

### 2. **Beautiful Output**
- Unicode box drawing for structure
- Emojis for visual scanning (📖 📚 👤 📅 📁 🏷️)
- Consistent formatting
- Readable typography

### 3. **Precision & Recall**
- Fuzzy matching catches typos
- Partial matching finds variations
- Cross-references find related work
- Multiple search strategies (author, topic, year, keyword)

### 4. **Extensibility**
- Modular architecture
- Multiple export formats
- Pluggable parsers
- API for programmatic use

### 5. **Lisp Philosophy**
- Data as code (S-expressions)
- Composable functions
- REPL-driven development
- Homoiconicity for meta-programming

## Future Enhancements

### Planned Features

- [ ] **Full-text search**: OCR PDFs, index contents
- [ ] **Citation graph**: Visualize paper relationships
- [ ] **BibTeX export**: For LaTeX documents
- [ ] **Web interface**: Browser-based exploration
- [ ] **API server**: HTTP REST API
- [ ] **Semantic search**: Topic modeling, embeddings
- [ ] **Recommendation engine**: "If you liked this..."
- [ ] **Version tracking**: Monitor library changes
- [ ] **Sync protocol**: Distributed library sharing

### Integration Ideas

- Emacs interface (via SLIME/Geiser)
- Command-line tools (grep-like paper search)
- Git hooks (auto-index on commit)
- MCP server (for Claude Code integration)

## Related Work

This directory system is inspired by:

- **Common Lisp HyperSpec**: Comprehensive, cross-referenced documentation
- **DSSA Architecture**: Distributed systems without central authority
- **SPKI/SDSI**: Local namespaces, authorization without identity
- **Xanadu**: Two-way links, transclusion, versioning

## Contributing

The cyberspace library is a personal research collection. However, the directory system itself is designed to be general-purpose.

To adapt for your own library:

1. Create INDEX.md files in your collections
2. Adjust parser for your metadata format
3. Customize display formatting
4. Add domain-specific search features

## License

"Peace for All Mankind"

This code is placed in the public domain. Use it freely, modify it joyfully, share it generously.

## Contact

Part of the cyberspace distributed systems research project.

---

**Happy exploring! May you find exactly what you need, and discover what you didn't know you were looking for.** 📚✨
