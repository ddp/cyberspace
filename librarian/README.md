# The Cyberspace Librarian

AI-powered search and discovery for the Library of Cyberspace.

## Architecture

```
┌─────────────────────────────────────────────────┐
│  Natural Language Query                         │
│  "Papers about hash-based crypto before PKI"   │
└──────────────────┬──────────────────────────────┘
                   │
                   ▼
┌─────────────────────────────────────────────────┐
│  Indexer (Chicken Scheme)                       │
│  - Walks ~/cyberspace/library/                  │
│  - Parses INDEX.md files                        │
│  - Extracts: titles, dates, authors, context    │
│  - Builds semantic index                        │
└──────────────────┬──────────────────────────────┘
                   │
                   ▼
┌─────────────────────────────────────────────────┐
│  Vector Store                                   │
│  - Embeddings of INDEX.md content               │
│  - SQLite database with metadata                │
│  - Fast similarity search                       │
└──────────────────┬──────────────────────────────┘
                   │
                   ▼
┌─────────────────────────────────────────────────┐
│  Query Engine (Chicken Scheme)                  │
│  - Semantic search via embeddings               │
│  - Temporal filtering (date ranges)             │
│  - Cross-reference traversal                    │
└──────────────────┬──────────────────────────────┘
                   │
                   ▼
┌─────────────────────────────────────────────────┐
│  Response Generator                             │
│  - LLM synthesis with retrieved context         │
│  - Citations to source papers                   │
│  - Temporal narratives ("evolution of X")       │
└─────────────────────────────────────────────────┘
```

## Components

### 1. `index-builder.scm` ✅
Walks library, parses INDEX.md files, builds searchable database.
- Recursively finds all INDEX.md files
- Extracts: titles, papers, years, authors, keywords
- Caches parsed index for fast access

### 2. `embedder.scm` ✅
Generates semantic embeddings (via local model or API).
- Ollama support (local, privacy-preserving)
- OpenAI API support (cloud-based)
- Cosine similarity for vector search
- Works without eggs (uses curl for HTTP)

### 3. `query.scm` ✅
CLI interface for natural language queries.
- Command-line: `./query.scm "your query"`
- Keyword search fallback (works without Ollama)
- REPL support for interactive use
- Example queries: `--demo`

### 4. `librarian.scm` (Planned)
Main orchestrator, ties everything together.

## Quick Start

```bash
# Build the index (first time)
cd ~/cyberspace/librarian
make index

# Search the library
./query.scm "Papers about hash-based crypto before PKI"
./query.scm "microkernels and formal verification"
./query.scm "one-time passwords"

# Run demo queries
./query.scm --demo

# Rebuild index after adding new papers
./query.scm --rebuild
```

## Dependencies (Chicken Eggs)

**Currently Required:**
- `srfi-1` - List utilities (standard)
- `srfi-13` - String utilities (standard)
- `irregex` - Regular expressions (standard)

**Optional (for future enhancements):**
- `sql-de-lite` - SQLite database for vector storage
- `http-client` - Native HTTP (currently using curl)
- `medea` - Robust JSON parsing (currently using simple parser)
- `args` - Advanced command-line parsing

