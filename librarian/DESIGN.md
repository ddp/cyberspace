# The Cyberspace Librarian - Design Document

## Vision

**"AI is the Dewey Decimal for the Library of Cyberspace"**

A natural language interface to discover and navigate the Library of Cyberspace, using AI to provide semantic search, temporal reasoning, and cross-domain connections.

## Phase 1: Index Building ✅ COMPLETE

**Status:** Working prototype in Chicken Scheme

**What It Does:**
- Walks `~/cyberspace/library/` recursively
- Finds all `INDEX.md` files (33 found)
- Parses metadata: titles, papers, years, authors, keywords
- Extracts full content for semantic analysis

**Output:** `library-index.txt` with structured data

**Code:** `index-builder.scm`

## Phase 2: Semantic Search (NEXT)

**Goal:** Enable queries like:
```
"Papers about hash-based crypto before PKI"
→ Finds: Lamport 1981, Merkle 1979
→ Context: Predates public-key infrastructure
→ Connection: Led to SPHINCS+ post-quantum signatures
```

**Architecture:**

```scheme
(define (semantic-search query library-index)
  ;; 1. Generate embedding for query
  (let ((query-embedding (embed-text query)))

    ;; 2. Find semantically similar content
    (let ((matches (find-similar library-index query-embedding)))

      ;; 3. Rank by relevance + temporal coherence
      (let ((ranked (rank-matches matches query)))

        ;; 4. Generate response with citations
        (generate-response ranked query)))))
```

**Options for Embeddings:**

**A. Local Model (Ollama):**
```scheme
(define (embed-text text)
  (http-post "http://localhost:11434/api/embeddings"
             `((model . "nomic-embed-text")
               (prompt . ,text))))
```

**B. OpenAI API:**
```scheme
(define (embed-text text)
  (http-post "https://api.openai.com/v1/embeddings"
             `((model . "text-embedding-3-small")
               (input . ,text))
             (headers `((Authorization . ,(string-append "Bearer " api-key))))))
```

**C. Claude API (via prompt):**
```scheme
(define (search-with-claude query context)
  (http-post "https://api.anthropic.com/v1/messages"
             `((model . "claude-sonnet-4-5-20250929")
               (messages . [((role . "user")
                             (content . ,(format-search-prompt query context)))]))))
```

**Vector Storage:**

```scheme
;; Simple SQLite schema
CREATE TABLE documents (
  id INTEGER PRIMARY KEY,
  path TEXT,
  collection TEXT,
  title TEXT,
  content TEXT,
  embedding BLOB  -- Serialized vector
);

CREATE TABLE papers (
  id INTEGER PRIMARY KEY,
  doc_id INTEGER,
  filename TEXT,
  title TEXT,
  year INTEGER,
  authors TEXT
);
```

## Phase 3: Temporal Reasoning

**Goal:** Navigate knowledge evolution

```scheme
(define (temporal-query start-year end-year topic)
  ;; "Show evolution of microkernels 1993-2014"
  ;;
  ;; 1993: Liedtke - IPC performance breakthrough
  ;; 1995: Liedtke - Minimality principle
  ;; 2009: seL4 - Formal verification begins
  ;; 2013: "From L3 to seL4" retrospective
  ;; 2014: seL4 verification complete
  )
```

**Implementation:**
- Extract year from metadata
- Build timeline of relevant papers
- Connect via citations and influence
- Generate narrative arc

## Phase 4: Cross-Domain Connections

**Goal:** Discover non-obvious relationships

```
Query: "How does Merkle connect to Git?"
→ Merkle trees (1979)
→ Content-addressable storage
→ Git uses SHA-1 Merkle trees
→ Also: Bitcoin, IPFS, Certificate Transparency

Query: "What connects NRL to Android?"
→ NRL develops OPIE (1995)
→ DTOS Flask architecture (1996)
→ NSA develops SELinux (2000)
→ Android mandates SELinux (2013)
```

**Implementation:**

```scheme
(define (find-connections entity-1 entity-2)
  ;; Build influence graph
  (let ((graph (build-citation-graph library-index)))

    ;; Find path between entities
    (let ((path (shortest-path graph entity-1 entity-2)))

      ;; Explain connections
      (explain-path path))))
```

## Phase 5: Natural Language Interface

**Goal:** Conversational exploration

```
User: "Tell me about verified systems"
Librarian: "The Library contains work on seL4 (verified OS kernel),
            CompCert (verified compiler), and the L4 microkernel
            family that made seL4 possible. Which interests you?"

User: "How does seL4 relate to L4?"
Librarian: "L4's minimality principle (Liedtke 1995) made seL4's
            formal verification tractable. The small kernel size
            (~9,700 lines) allowed complete mathematical proof.
            See: l4-microkernel/liedtke-microkernel-construction-1995.pdf"
```

**Implementation:**

```scheme
(define (chat query conversation-history)
  ;; Maintain conversation state
  ;; Retrieve relevant context
  ;; Generate response with citations
  ;; Update history
  )
```

## Technology Stack

**Core:** Chicken Scheme
- Elegant functional programming
- Compiles to C (fast)
- Good FFI for C libraries
- Active community

**Dependencies (Chicken Eggs):**
- `sql-de-lite` - SQLite database
- `http-client` - API calls
- `medea` - JSON parsing
- `irregex` - Pattern matching
- `srfi-1, srfi-13` - Utilities

**External Services:**
- **Ollama** (local LLM) - Recommended
- **OpenAI API** (embeddings)
- **Claude API** (response generation)

## Design Principles

### 1. Offline-First
- Local index on each machine (om, fluffy, lambda)
- Git-synced library
- Optional cloud APIs for enhancement

### 2. Incremental Enhancement
- Phase 1 works standalone (text search)
- Phase 2 adds semantics (embeddings)
- Phase 3 adds time (narratives)
- Phase 4 adds graphs (connections)
- Each phase adds value independently

### 3. Respect for Sources
- Always cite original papers
- Link to Internet Archive
- Preserve provenance
- "Standing on shoulders of giants"

### 4. Schemer's Aesthetic
- Elegant code > complex code
- Compose simple functions
- Data structures over algorithms
- REPLdriven development

## Example Queries (When Complete)

**Discovery:**
```
"Papers about one-time passwords"
→ Lamport 1981, OPIE (NRL 1995), RFC 1938, RFC 2289
→ Connection: Hash chains for authentication
→ Modern: TOTP (Google Authenticator)
```

**Evolution:**
```
"How did Merkle's work lead to post-quantum crypto?"
→ 1979: Merkle trees (hash-based)
→ 1981: Lamport signatures (hash-based)
→ 2015: SPHINCS+ (stateless hash signatures)
→ 2024: NIST FIPS 205 (post-quantum standard)
→ Key insight: Hash-based crypto survives quantum attack
```

**Cross-Domain:**
```
"What connects DEC to modern IDEs?"
→ DECset (1980s): Language-Sensitive Editor
→ Concept: Syntax-aware editing, code intelligence
→ Influence: Visual Studio IntelliSense
→ Modern: Language Server Protocol
→ The ideas from 40 years ago live on!
```

**Expert Queries:**
```
"Papers by researchers who worked on both crypto and OS security"
→ Lampson (CAP system, key distribution)
→ Connection: Capability systems = unforgeable keys
→ Cross-domain insight: Same math, different layers
```

## Next Steps

1. **Implement embeddings** (Phase 2)
   - Choose: Ollama (local) or OpenAI API
   - Generate embeddings for all INDEX.md content
   - Store in SQLite with metadata

2. **Build query interface** (Phase 2)
   - CLI: `librarian "query text"`
   - Interactive: REPL with conversation

3. **Add temporal reasoning** (Phase 3)
   - Timeline generation
   - Evolution narratives

4. **Implement graph traversal** (Phase 4)
   - Build citation/influence graph
   - Find connections

5. **Polish UX** (Phase 5)
   - Natural conversation
   - Formatted output
   - Web interface?

## Status

**✅ Phase 1 Complete:** Index building works, 33 collections indexed

**🚧 Phase 2 In Progress:** Next - add semantic search

**📋 Phase 3-5 Planned:** Temporal reasoning, connections, chat interface

---

**"The goal is not just to find papers, but to understand the evolution of ideas across decades of computer science research."**
