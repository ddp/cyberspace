;; Auto-converted from Markdown
;; Review and edit as needed

(rfc
  (number 25)
  (title "Soup Query Language")
  (section
    "Abstract"
    (p "This RFC specifies the query language for the Library of Cyberspace soup: how principals search, filter, and retrieve objects from the content-addressed store using the rich metadata layer. Queries are themselves content-addressed and auditable."))
  (section
    "Motivation"
    (p "The soup contains infinite metadata. Finding needles requires a query language that is:")
    (list
      (item "Expressive")
      (item "Complex predicates, joins across objects")
      (item "Efficient")
      (item "Indexes, bloom filters, query planning")
      (item "Secure")
      (item "Queries respect capability boundaries")
      (item "Auditable")
      (item "Query patterns reveal access patterns"))
    (p "Newton's soup had cursor-based queries. We extend this with content-addressed semantics."))
  (section
    "Query Model"
    (subsection
      "Basic Queries"
      (code scheme ";; Find by type\n(soup-query type: 'document)\n\n;; Find by attribute\n(soup-query author: \"alice@example.com\")\n\n;; Find by multiple attributes (AND)\n(soup-query type: 'document\n            author: \"alice@example.com\"\n            created-after: \"2026-01-01\")\n\n;; Find by content hash\n(soup-query hash: \"sha256:7f83b1657ff1fc...\")"))
    (subsection
      "Query Results"
      (code scheme ";; Results are lazy cursors\n(define results (soup-query type: 'document))\n\n;; Iterate\n(soup-cursor-next results)    ; => soup-object or #f\n(soup-cursor-peek results)    ; => next without advancing\n(soup-cursor-reset results)   ; => back to beginning\n\n;; Collect (careful with large result sets)\n(soup-cursor->list results)   ; => list of soup-objects\n(soup-cursor-count results)   ; => total count"))
    (subsection
      "Predicates"
      (code scheme ";; Comparison operators\n(soup-query size: (> 1000000))           ; larger than 1MB\n(soup-query created: (< \"2025-01-01\"))   ; before 2025\n(soup-query name: (like \"rfc-*\"))        ; glob pattern\n(soup-query tags: (contains \"urgent\"))   ; list membership\n\n;; Logical operators\n(soup-query (and (type: 'document)\n                 (or (author: \"alice\")\n                     (author: \"bob\"))))\n\n;; Negation\n(soup-query (not (type: 'tombstone)))\n\n;; Existence\n(soup-query (exists 'encryption-key))    ; has attribute\n(soup-query (missing 'expires))          ; lacks attribute")))
  (section
    "Advanced Queries"
    (subsection
      "Range Queries"
      (code scheme ";; Numeric ranges\n(soup-query size: (between 1000 10000))\n\n;; Date ranges\n(soup-query created: (between \"2026-01-01\" \"2026-12-31\"))\n\n;; Lexicographic ranges\n(soup-query name: (between \"rfc-010\" \"rfc-020\"))"))
    (subsection
      "Full-Text Search"
      (code scheme ";; Search indexed content\n(soup-query (text-search \"capability delegation\"))\n\n;; With highlighting\n(soup-query (text-search \"SPKI certificate\")\n            highlight: #t)\n\n;; Phrase search\n(soup-query (text-search \"\\\"monotonic attenuation\\\"\"))\n\n;; Fuzzy search\n(soup-query (text-search \"delgation~\"))  ; typo-tolerant"))
    (subsection
      "Reference Traversal"
      (code scheme ";; Objects referencing this hash\n(soup-query references: \"sha256:target...\")\n\n;; Objects referenced by this hash\n(soup-query referenced-by: \"sha256:source...\")\n\n;; Transitive closure (careful - can be huge)\n(soup-query (transitive-references \"sha256:root...\")\n            max-depth: 3)"))
    (subsection
      "Temporal Queries"
      (code scheme ";; Objects as they existed at a point in time\n(soup-query type: 'document\n            as-of: \"2026-01-01T00:00:00Z\")\n\n;; Objects modified in time window\n(soup-query modified: (between \"2026-01-01\" \"2026-01-07\"))\n\n;; Version history\n(soup-query (versions-of \"sha256:current...\"))")))
  (section
    "Query Composition"
    (subsection
      "Subqueries"
      (code scheme ";; Objects authored by members of a group\n(soup-query author: (soup-query type: 'principal\n                                member-of: \"engineering\"))\n\n;; Documents referencing any RFC\n(soup-query type: 'document\n            references: (soup-query name: (like \"rfc-*\")))"))
    (subsection
      "Aggregation"
      (code scheme ";; Count by type\n(soup-aggregate\n  group-by: 'type\n  aggregate: (count))\n\n;; Total size by author\n(soup-aggregate\n  group-by: 'author\n  aggregate: (sum 'size))\n\n;; Average document size\n(soup-aggregate\n  where: (type: 'document)\n  aggregate: (avg 'size))\n\n;; Distinct values\n(soup-aggregate\n  aggregate: (distinct 'content-type))"))
    (subsection
      "Ordering and Pagination"
      (code scheme ";; Sort by creation date, newest first\n(soup-query type: 'document\n            order-by: '((created desc)))\n\n;; Multi-column sort\n(soup-query type: 'document\n            order-by: '((author asc) (created desc)))\n\n;; Pagination\n(soup-query type: 'document\n            order-by: '((created desc))\n            limit: 20\n            offset: 40)\n\n;; Cursor-based pagination (more efficient)\n(soup-query type: 'document\n            order-by: '((created desc))\n            after: \"sha256:last-seen...\")")))
  (section
    "Capability-Aware Queries"
    (subsection
      "Query Filtering"
      (p "Queries automatically filter results based on the querying principal's capabilities:")
      (code scheme "(define (soup-query-with-caps query principal)\n  \"Execute query filtered by principal's capabilities\"\n  (let* ((raw-results (execute-query query))\n         (caps (principal-capabilities principal)))\n    (filter (lambda (obj)\n              (can-read? principal obj caps))\n            raw-results)))"))
    (subsection
      "Capability Queries"
      (code scheme ";; What can I access?\n(soup-query (accessible-by (current-principal)))\n\n;; Who can access this?\n(soup-query type: 'certificate\n            grants-access-to: \"sha256:target...\")\n\n;; Find my capabilities\n(soup-query type: 'certificate\n            subject: (current-principal))"))
    (subsection
      "Query Authorization"
      (code scheme ";; Some queries require explicit capability\n(soup-query type: 'audit-log)  ; requires audit-read capability\n\n;; Query capability certificate\n(spki-cert\n  (issuer vault-admin)\n  (subject auditor-key)\n  (capability\n    (action query)\n    (object (type 'audit-log)))\n  (validity (not-after \"2027-01-01\")))")))
  (section
    "Indexes"
    (subsection
      "Index Types"
      (code scheme ";; B-tree index (ordered, range queries)\n(define-index 'created-idx\n  type: 'btree\n  on: 'created)\n\n;; Hash index (equality only, faster)\n(define-index 'hash-idx\n  type: 'hash\n  on: 'content-hash)\n\n;; Full-text index (search)\n(define-index 'content-idx\n  type: 'fulltext\n  on: 'content\n  language: 'english)\n\n;; Composite index\n(define-index 'author-date-idx\n  type: 'btree\n  on: '(author created))\n\n;; Bloom filter index (membership testing)\n(define-index 'tags-bloom\n  type: 'bloom\n  on: 'tags\n  false-positive-rate: 0.01)"))
    (subsection
      "Cost-Based Index Selection"
      (p "Query planning uses Selinger-style cost estimation to select optimal execution plans. The optimizer considers:")
      (list
        (item "Cardinality estimation: How many rows will each predicate return?")
        (item "Index selectivity: How discriminating is each index?")
        (item "I/O cost: Sequential scan vs. random access")
        (item "Join ordering: Which order minimizes intermediate result sizes?"))
      (code scheme ";; Cardinality estimation using histograms\n(define (estimate-cardinality predicate index-stats)\n  \"Estimate result size for predicate\"\n  (let ((histogram (index-histogram index-stats)))\n    (case (predicate-type predicate)\n      ((equality)\n       ;; Use histogram bucket counts\n       (histogram-point-estimate histogram (predicate-value predicate)))\n      ((range)\n       ;; Sum histogram buckets in range\n       (histogram-range-estimate histogram\n                                  (predicate-low predicate)\n                                  (predicate-high predicate)))\n      ((like)\n       ;; Estimate based on prefix selectivity\n       ( (total-rows index-stats)\n          (prefix-selectivity (predicate-pattern predicate))))\n      (else\n       ;; Conservative estimate: 10% of total\n       ( 0.1 (total-rows index-stats))))))\n\n;; Cost model for execution plans\n(define (plan-cost plan index-stats)\n  \"Estimate total cost in I/O operations\"\n  (let ((cardinality (estimate-cardinality (plan-predicate plan) index-stats)))\n    (case (plan-access-method plan)\n      ((full-scan)\n       ;; Sequential I/O: count all pages\n       (total-pages index-stats))\n      ((index-scan)\n       ;; Random I/O: estimated rows + index traversal\n       (+ (log2 (total-rows index-stats))  ; B-tree depth\n          cardinality))                     ; Heap fetches\n      ((index-only)\n       ;; No heap access needed\n       (log2 (total-rows index-stats)))\n      ((bloom-filter)\n       ;; O(k) hash operations, negligible I/O\n       ( 0.001 cardinality)))))\n\n;; Dynamic programming for join ordering\n(define (optimize-join-order predicates indexes)\n  \"Find optimal join order using Selinger algorithm\"\n  (let ((memo (make-hash-table)))\n    (define (best-plan preds)\n      (cond\n        ((null? preds) (empty-plan))\n        ((hash-table-exists? memo preds)\n         (hash-table-ref memo preds))\n        (else\n         (let ((candidates\n                 (map (lambda (p)\n                        (let ((rest (delete p preds)))\n                          (join-plans (single-predicate-plan p)\n                                      (best-plan rest))))\n                      preds))\n                (best (minimum-by plan-cost candidates)))\n           (hash-table-set! memo preds best)\n           best))))\n    (best-plan predicates)))\n\n;; Select best index for query\n(define (plan-query query indexes)\n  \"Generate optimal query plan using cost-based optimization\"\n  (let ((predicates (query-predicates query))\n         (stats (map index-statistics indexes))\n         ;; Generate candidate plans\n         (candidates\n          (append\n           ;; Try each applicable index\n           (filter-map (lambda (idx stat)\n                        (and (index-covers? idx predicates)\n                             (make-plan 'index-scan idx\n                                        (plan-cost-for idx predicates stat))))\n                      indexes stats)\n           ;; Always consider full scan\n           (list (make-plan 'full-scan #f (full-scan-cost predicates stats)))))\n         ;; Select minimum cost plan\n         (best (minimum-by plan-cost candidates)))\n    (when (> (plan-cost best) query-cost-warning-threshold*)\n      (log-warning \"Expensive query plan\" query (plan-cost best)))\n    best))"))
    (subsection
      "Histogram Maintenance"
      (code scheme ";; Equi-depth histograms for cardinality estimation\n(define (build-histogram values num-buckets)\n  \"Build equi-depth histogram for cardinality estimation\"\n  (let ((sorted (sort values <))\n         (bucket-size (ceiling (/ (length sorted) num-buckets)))\n         (boundaries (map (lambda (i)\n                           (list-ref sorted ( i bucket-size)))\n                         (iota num-buckets))))\n    (make-histogram boundaries (/ (length sorted) num-buckets))))\n\n;; Update histogram incrementally\n(define (histogram-update! hist value)\n  \"Incrementally update histogram with new value\"\n  (let ((bucket (find-bucket hist value)))\n    (bucket-increment! bucket)))\n\n;; Statistics refresh\n(define (refresh-index-statistics idx)\n  \"Rebuild index statistics (run periodically)\"\n  (let* ((samples (index-sample idx 10000))  ; Sample 10K rows\n         (histogram (build-histogram samples 100)))\n    (set-index-statistics! idx\n      (make-stats\n        (total-rows (index-count idx))\n        (distinct-values (length (delete-duplicates samples)))\n        (histogram histogram)\n        (last-analyzed (current-time))))))"))
    (subsection
      "Index Maintenance"
      (code scheme ";; Indexes are updated on soup-put\n(define (soup-put-indexed obj)\n  (let ((hash (soup-put obj)))\n    (for-each (lambda (idx)\n                (index-insert! idx obj hash))\n              (applicable-indexes obj))\n    hash))\n\n;; Periodic index optimization\n(define (optimize-indexes)\n  (for-each index-compact! (all-indexes)))")))
  (section
    "Query Execution"
    (subsection
      "Query Planning"
      (code scheme "(define (execute-query query)\n  \"Plan and execute query\"\n  (let ((plan (plan-query query))\n         (cost (estimate-cost plan)))\n    (when (> cost query-cost-limit*)\n      (error \"Query too expensive\" cost))\n    (execute-plan plan)))\n\n(define (plan-query query)\n  \"Generate query execution plan\"\n  `(query-plan\n    (predicates ,(query-predicates query))\n    (index ,(select-index query))\n    (filter ,(remaining-predicates query))\n    (order ,(query-order query))\n    (limit ,(query-limit query))))"))
    (subsection
      "Execution Strategies"
      (code scheme ";; Index scan\n(define (index-scan index predicate)\n  (index-range-query index\n                     (predicate-lower-bound predicate)\n                     (predicate-upper-bound predicate)))\n\n;; Full scan (last resort)\n(define (full-scan predicate)\n  (filter predicate (all-soup-objects)))\n\n;; Index intersection\n(define (index-intersect idx1 idx2 pred1 pred2)\n  (set-intersection\n    (index-scan idx1 pred1)\n    (index-scan idx2 pred2)))"))
    (subsection
      "Query Caching"
      (p "The soup is archival - objects rarely change, making aggressive caching safe.")
      (code scheme ";; Multi-tier cache: L1 hot results, L2 warm, L3 persistent\n(define l1-cache (make-lru-cache 100))    ; In-memory, microseconds\n(define l2-cache (make-lru-cache 10000))  ; Warm, milliseconds\n(define l3-cache 'persistent-index)        ; On-disk, query index\n\n(define (cached-query query principal)\n  \"Multi-tier cached query with capability awareness\"\n  (let ((key (query-cache-key query principal)))\n    (or (lru-get l1-cache key)\n        (lru-get l2-cache key)\n        (persistent-cache-get l3-cache key)\n        (let ((result (execute-query query)))\n          ;; Promote to appropriate cache tier based on cost\n          (let ((cost (query-cost query)))\n            (cond\n              ((> cost 1000) (persistent-cache-put! l3-cache key result))\n              ((> cost 100) (lru-put! l2-cache key result))\n              (else (lru-put! l1-cache key result))))\n          result))))")
      (p "#### Dependency-Based Invalidation")
      (p "Track which predicates affect which cached queries using Bloom filters:")
      (code scheme ";; Bloom filter tracking which attributes affect cached queries\n(define query-dependencies (make-counting-bloom-filter 100000 0.001))\n\n(define (cache-with-deps query result)\n  \"Cache query and track its dependencies\"\n  (let ((key (query->hash query))\n        (deps (query-attribute-deps query)))\n    (lru-put! query-cache key result)\n    ;; Track dependencies\n    (for-each (lambda (attr)\n                (bloom-add! query-dependencies (cons attr key)))\n              deps)))\n\n(define (invalidate-on-change obj)\n  \"Invalidate only queries that MIGHT be affected (conservative)\"\n  (let ((attrs (soup-object-attributes obj)))\n    (for-each (lambda (attr)\n                ;; Check if any cached query depends on this attribute\n                (when (bloom-might-contain? query-dependencies attr)\n                  (invalidate-queries-for-attribute attr)))\n              attrs)))")
      (p "#### Archival Cache Semantics")
      (p "For the soup's archival nature, implement copy-on-write cache entries:")
      (code scheme ";; Immutable cache entries - archival objects never change\n(define (archival-cache-get cache hash)\n  \"Archival objects can be cached permanently\"\n  (let ((entry (hash-table-ref cache hash #f)))\n    (if entry\n        (if (archival-generation? (soup-get hash))\n            entry  ; Archival: never expires\n            (if (cache-entry-fresh? entry)\n                (cache-entry-value entry)\n                #f))  ; Non-archival: check freshness\n        #f)))\n\n;; Generation-aware caching\n(define (cache-ttl-for-generation gen)\n  (case gen\n    ((archival) +inf.0)       ; Never expires\n    ((stable) 86400)          ; 1 day\n    ((maturing) 3600)         ; 1 hour\n    ((young) 60)              ; 1 minute\n    ((ephemeral) 0)))         ; No caching")))
  (section
    "Distributed Queries"
    (subsection
      "Federated Query"
      (code scheme ";; Query across multiple vaults\n(soup-query type: 'document\n            federation: '(vault-a vault-b vault-c))\n\n;; Query with locality preference\n(soup-query type: 'document\n            prefer-local: #t)"))
    (subsection
      "Query Routing"
      (code scheme "(define (route-query query vaults)\n  \"Route query to appropriate vaults\"\n  (let ((partitions (query-partitions query)))\n    (map (lambda (vault)\n           (list vault (subquery-for-vault query vault)))\n         (filter (lambda (v)\n                   (vault-has-partition? v partitions))\n                 vaults))))"))
    (subsection
      "Result Merging"
      (code scheme "(define (merge-results results order)\n  \"Merge sorted results from multiple vaults\"\n  (let ((streams (map result->stream results)))\n    (merge-sorted-streams streams (order->comparator order))))")))
  (section
    "Query Audit"
    (subsection
      "Audit Trail"
      (code scheme ";; All queries are logged\n(define (audited-query query principal)\n  (let ((start (current-time))\n        (result (soup-query-with-caps query principal)))\n    (audit-append\n      action: 'query\n      principal: principal\n      query: (query->sexp query)\n      result-count: (soup-cursor-count result)\n      duration: (- (current-time) start))\n    result))"))
    (subsection
      "Query Analysis"
      (code scheme ";; Analyze query patterns\n(soup-query type: 'audit-entry\n            action: 'query\n            principal: \"alice\")\n\n;; Find expensive queries\n(soup-query type: 'audit-entry\n            action: 'query\n            duration: (> 1000))  ; > 1 second\n\n;; Access pattern analysis\n(soup-aggregate\n  where: (and (type: 'audit-entry) (action: 'query))\n  group-by: 'principal\n  aggregate: (count))")))
  (section
    "Query Language Grammar"
    (code "query       ::= (soup-query clause)\nclause      ::= attribute-clause | predicate-clause | option-clause\nattribute   ::= symbol ':' value\npredicate   ::= '(' op value ')'\nop          ::= '>' | '<' | '>=' | '<=' | '=' | '!='\n              | 'like' | 'between' | 'contains'\n              | 'and' | 'or' | 'not'\n              | 'exists' | 'missing'\n              | 'text-search' | 'references' | 'referenced-by'\noption      ::= 'order-by' | 'limit' | 'offset' | 'after'\n              | 'as-of' | 'highlight' | 'federation'\nvalue       ::= string | number | boolean | hash | query"))
  (section
    "Security Considerations"
    (subsection
      "Query Injection"
      (code scheme ";; Never interpolate user input into queries\n;; BAD:\n(soup-query name: (string-append \"rfc-\" user-input))\n\n;; GOOD:\n(soup-query name: (like (sanitize-pattern user-input)))\n\n(define (sanitize-pattern s)\n  (string-map (lambda (c)\n                (if (member c '(#\\* #\\? #\\[ #\\]))\n                    #\\\\\n                    c))\n              s))"))
    (subsection
      "Query Cost Limits"
      (code scheme ";; Prevent denial of service via expensive queries\n(define query-cost-limit 10000)\n(define query-timeout 30)  ; seconds\n\n(define (safe-query query)\n  (with-timeout query-timeout\n    (let ((cost (estimate-cost query)))\n      (when (> cost query-cost-limit)\n        (error \"Query exceeds cost limit\"))\n      (execute-query query))))"))
    (subsection
      "Information Leakage"
      (code scheme ";; Query existence can leak information\n;; Even \"not found\" reveals something\n\n;; Use constant-time responses for sensitive queries\n(define (private-query query)\n  (let ((result (soup-query query)))\n    (if (authorized? (current-principal) result)\n        result\n        (constant-time-not-found))))")))
  (section
    "Implementation Notes"
    (subsection
      "Performance"
      (list
        (item "Index selection is critical for large soups")
        (item "Bloom filters for fast negative lookups")
        (item "Query result streaming to avoid memory exhaustion")
        (item "Connection pooling for federated queries")))
    (subsection
      "Compatibility"
      (list
        (item "Query language inspired by Newton's soup cursors")
        (item "SQL-like semantics where applicable")
        (item "S-expression syntax for Scheme integration"))))
  (section
    "References"
    (p "1. Newton Programmer's Guide - Soup and cursor APIs 2. SQLite Query Planner - Query optimization 3. Selinger et al., \"Access Path Selection in a Relational Database Management System\" (1979) - Cost-based optimization 4. RFC-020: Content-Addressed Storage 5. RFC-021: Capability Delegation 6. RFC-026: Garbage Collection (generation-aware caching)"))
  (section
    "Changelog"
    (list
      (item "2026-01-09")
      (item "Cost-based query optimization: Selinger algorithm, cardinality estimation, histograms, multi-tier caching with generation-aware TTL - 2026-01-07")
      (item "Initial draft"))))

