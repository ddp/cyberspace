;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 9)
  (title "Library Directory System")
  (section
    "Abstract"
    (p "This Memo specifies the Library Directory System for the Library of Cyberspace: a searchable catalog of research papers with natural language queries, fuzzy matching, and beautiful output. Finding knowledge should be delightful."))
  (section
    "E Pluribus Unum"
    (code "╔═══════════════════════════════════════════════════════════════╗\n║  📚 Cyberspace Library Directory                               ║\n║  Finding knowledge should be joyful                            ║\n╚═══════════════════════════════════════════════════════════════╝"))
  (section
    "Motivation"
    (p "The Library of Cyberspace contains 421+ research papers spanning 50 years of computing history. Without a catalog:")
    (list
      (item "Discoverability: How to find Lamport's clock paper?")
      (item "Connections: What relates to SPKI?")
      (item "Context: When was this written? By whom?"))
    (p "The Directory System provides:")
    (p "1. Natural language search - \"papers by Lampson about protection\" 2. Multi-index access - By author, topic, year, collection 3. Fuzzy matching - \"Lamp\" finds Lampson and Lamport 4. Beautiful output - Unicode, emoji, formatted results 5. S-expression export - Machine-readable catalogs"))
  (section
    "Data Model"
    (subsection
      "Document Record"
      (code scheme "(define-record-type <document>\n  (make-document title authors year topics file-path\n                 collection source-url description)\n  document?\n  (title document-title)\n  (authors document-authors)      ; List of strings\n  (year document-year)            ; Integer or #f\n  (topics document-topics)        ; List of strings\n  (file-path document-file-path)\n  (collection document-collection)\n  (source-url document-source-url)\n  (description document-description))"))
    (subsection
      "Collection Record"
      (code scheme "(define-record-type <collection>\n  (make-collection name path documents description)\n  collection?\n  (name collection-name)\n  (path collection-path)\n  (documents collection-documents)  ; List of documents\n  (description collection-description))"))
    (subsection
      "Library Record"
      (code scheme "(define-record-type <library>\n  (make-library collections documents\n                author-index topic-index year-index collection-index)\n  library?\n  (collections library-collections)\n  (documents library-documents)\n  (author-index library-author-index)     ; Hash table\n  (topic-index library-topic-index)       ; Hash table\n  (year-index library-year-index)         ; Hash table\n  (collection-index library-collection-index))")))
  (section
    "Index System"
    (p "Four hash table indexes for O(1) lookup:")
    (code "author-index:     \"Lamport\" → [doc1, doc2, doc5, ...]\ntopic-index:      \"cryptography\" → [doc3, doc7, doc12, ...]\nyear-index:       1978 → [doc1, doc4, ...]\ncollection-index: \"lampson\" → <collection>")
    (subsection
      "Building Indexes"
      (code scheme "(define (build-author-index documents)\n  (let ((index (make-hash-table equal?)))\n    (for-each\n      (lambda (doc)\n        (for-each\n          (lambda (author)\n            (hash-table-update!/default\n              index\n              (normalize-author author)\n              (lambda (docs) (cons doc docs))\n              '()))\n          (document-authors doc)))\n      documents)\n    index))")))
  (section
    "Query Interface"
    (subsection
      "Natural Language Parsing"
      (code scheme "(parse-query \"papers by Lampson about protection\")\n;; => (query (author \"Lampson\") (topic \"protection\"))\n\n(parse-query \"from 1978\")\n;; => (query (year 1978))\n\n(parse-query \"SPKI certificates\")\n;; => (query (topic \"SPKI\") (topic \"certificates\"))")
      (p "Recognized Patterns: - by <name> → author search - about <topic> → topic search - from <year> → year search - in <collection> → collection filter - Bare words → topic search"))
    (subsection
      "Fuzzy Matching"
      (code scheme "(fuzzy-match \"Lamp\" author-list)\n;; => (\"Lampson\" \"Lamport\")\n\n(fuzzy-match \"crypto\" topic-list)\n;; => (\"cryptography\" \"cryptographic\" \"encryption\")")
      (p "Matching strategies: 1. Exact match (highest priority) 2. Case-insensitive match 3. Prefix match 4. Substring match"))
    (subsection
      "Query Functions"
      (code scheme "(find-by-author library \"Lampson\")\n(find-by-topic library \"SPKI\")\n(find-by-year library 1978)\n(find-by-collection library \"lampson\")\n(find-related library document)")))
  (section
    "REPL Interface"
    (subsection
      "Interactive Session"
      (code "$ csi -s directory-repl.scm\n\n╔═══════════════════════════════════════════════════════════════╗\n║  📚 Cyberspace Library Directory                               ║\n║  \"E Pluribus Unum\" - Finding knowledge should be joyful        ║\n╚═══════════════════════════════════════════════════════════════╝\n\nLoaded 312 documents from 18 collections\nType 'help' for search tips, 'quit' to exit\n\n📖 > papers by Rivest\n\n📚 Found 3 documents:\n\n [1] SDSI: A Simple Distributed Security Infrastructure\n     👤 R. Rivest, B. Lampson\n     📅 1996  📁 lampson\n\n [2] SPKI Certificate Theory\n     👤 C. Ellison, B. Frantz, B. Lampson, R. Rivest, ...\n     📅 1999  📁 lampson\n\n📖 > about SPKI\n\n📚 Found 8 documents:\n...\n\n📖 > stats\n\nLibrary Statistics:\n  📚 Documents: 312\n  📁 Collections: 18\n  👤 Authors: 245\n  🏷️ Topics: 89\n  📅 Years: 1971-2024\n\n📖 > quit\nHappy exploring! 📚✨"))
    (subsection
      "Commands"
      (table
        (header "Command " "Description ")
        (row "help " "Show search tips ")
        (row "stats " "Library statistics ")
        (row "collections " "List all collections ")
        (row "authors " "Show author index ")
        (row "topics " "Show topic index ")
        (row "years " "Show year distribution ")
        (row "quit " "Exit REPL "))))
  (section
    "INDEX.md Parser"
    (p "Each collection contains an INDEX.md with paper listings:")
    (code markdown "# Lampson Collection\n\nButler Lampson's papers on protection, capability systems, and distributed computing.\n\n## Papers\n\n1. Protection (1971)\n   - Author: Butler Lampson\n   - Topics: capability, protection, access control\n   - Source: ACM Operating Systems Review\n\n2. Hints for Computer System Design (1983)\n   - Author: Butler Lampson\n   - Topics: systems design, engineering\n   - Source: ACM Operating Systems Review")
    (subsection
      "Parser Output"
      (code scheme "(parse-index-file \"lampson/INDEX.md\")\n;; =>\n(collection\n  (name \"lampson\")\n  (description \"Butler Lampson's papers...\")\n  (documents\n    ((title \"Protection\")\n     (authors \"Butler Lampson\")\n     (year 1971)\n     (topics \"capability\" \"protection\" \"access control\"))\n    ...))")))
  (section
    "Export Formats"
    (subsection
      "S-expression Export"
      (code scheme "(export-to-sexp library \"catalog.sexp\")")
      (p "Output:")
      (code scheme "(library\n  (metadata\n    (document-count 312)\n    (collection-count 18)\n    (generated \"2026-01-06\"))\n  (collections\n    (collection\n      (name \"lampson\")\n      (documents\n        (document\n          (title \"Protection\")\n          (authors (\"Butler Lampson\"))\n          (year 1971)\n          (topics (\"capability\" \"protection\")))\n        ...))\n    ...))"))
    (subsection
      "HTML Export"
      (code scheme "(export-to-html library \"catalog.html\")")
      (p "Generates browsable web catalog with: - Alphabetical author index - Topic tag cloud - Year timeline - Search functionality"))
    (subsection
      "Markdown Export"
      (code scheme "(export-to-markdown library \"catalog.md\")")
      (p "Documentation-friendly format for README files.")))
  (section
    "Design Philosophy"
    (subsection
      "Super Nice and Helpful"
      (list
        (item "Natural language understanding")
        (item "Fuzzy matching catches typos")
        (item "Suggestions for empty results")
        (item "Encouraging prompts")))
    (subsection
      "Beautiful Output"
      (list
        (item "Unicode box drawing (╔═══╗)")
        (item "Emoji visual markers (📖 📚 👤 📅)")
        (item "Consistent formatting")
        (item "Progressive disclosure")))
    (subsection
      "Hone In On What You Need"
      (list
        (item "Multi-strategy search")
        (item "Progressive filtering")
        (item "Cross-references")
        (item "Related paper discovery"))))
  (section
    "Security Considerations"
    (subsection
      "No Execution"
      (p "The directory system is read-only: - Parses INDEX.md files (trusted) - No code execution - No network access - No file modification"))
    (subsection
      "Path Traversal"
      (p "File paths validated: - Must be within library root - No .. components - Normalized before use")))
  (section
    "Implementation Notes"
    (subsection
      "Dependencies"
      (list
        (item "srfi-1")
        (item "List utilities - srfi-13")
        (item "String utilities - srfi-69")
        (item "Hash tables - chicken file")
        (item "Directory scanning")))
    (subsection
      "Performance"
      (list
        (item "Index building: O(N) documents")
        (item "Query: O(1) hash lookup + O(M) result filtering")
        (item "Fuzzy match: O(K) candidates")))
    (subsection
      "Extensibility"
      (p "Future enhancements: - Full-text search (PostScript/Text extraction) - Citation graph visualization - BibTeX export - Web API server - Semantic search with embeddings")))
  (section
    "References"
    (p "1. Dublin Core Metadata Initiative 2. Library of Congress Subject Headings 3. BibTeX format specification 4. Unicode Standard for box drawing"))
  (section
    "Changelog"
    (list
      (item "2026-01-06")
      (item "Initial specification"))))

