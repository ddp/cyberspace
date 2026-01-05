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

### 1. `index-builder.scm`
Walks library, parses INDEX.md files, builds searchable database.

### 2. `embedder.scm`
Generates semantic embeddings (via local model or API).

### 3. `query.scm`
CLI interface for natural language queries.

### 4. `librarian.scm`
Main orchestrator, ties everything together.

## Dependencies (Chicken Eggs)

- `sql-de-lite` - SQLite database
- `http-client` - API calls for embeddings/LLM
- `medea` - JSON parsing
- `irregex` - Regular expressions
- `srfi-1` - List utilities
- `srfi-13` - String utilities
- `args` - Command-line argument parsing

