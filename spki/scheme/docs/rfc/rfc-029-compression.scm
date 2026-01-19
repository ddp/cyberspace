;; Auto-converted from Markdown
;; Review and edit as needed

(rfc
  (number 29)
  (title "Compression and Deduplication")
  (section
    "Abstract"
    (p "This RFC specifies compression and deduplication for the Library of Cyberspace: how vaults reduce storage requirements while maintaining content-addressability, integrity verification, and efficient retrieval. Compression is transparent to the content-addressing layer."))
  (section
    "Motivation"
    (p "Storage efficiency matters for preservation:")
    (list
      (item "Cost")
      (item "Less storage means more preservation per dollar")
      (item "Bandwidth")
      (item "Compressed transfers are faster")
      (item "Redundancy")
      (item "More copies fit in same space")
      (item "Longevity")
      (item "Smaller archives survive longer"))
    (p "But compression must not compromise:")
    (list
      (item "Integrity")
      (item "Hashes must remain valid")
      (item "Addressability")
      (item "Content addressing still works")
      (item "Deduplication")
      (item "Identical content stored once")
      (item "Accessibility")
      (item "Data remains retrievable")))
  (section
    "Compression Model"
    (subsection
      "Layered Architecture"
      (code "┌─────────────────────────────────────┐\n│         Application Layer           │\n│     (sees uncompressed data)        │\n├─────────────────────────────────────┤\n│        Content-Addressing           │\n│    (hash of uncompressed data)      │\n├─────────────────────────────────────┤\n│        Compression Layer            │\n│      (transparent compression)      │\n├─────────────────────────────────────┤\n│         Storage Layer               │\n│     (stores compressed data)        │\n└─────────────────────────────────────┘"))
    (subsection
      "Compression Metadata"
      (code scheme "(define (compress-object data algorithm)\n  (let* ((compressed (compress algorithm data))\n         (ratio (/ (bytevector-length compressed)\n                   (bytevector-length data))))\n    `(compressed-object\n      (algorithm ,algorithm)\n      (original-size ,(bytevector-length data))\n      (compressed-size ,(bytevector-length compressed))\n      (ratio ,ratio)\n      (data ,compressed))))\n\n;; Stored in soup\n(soup-object\n  (hash \"sha256:original-content-hash...\")\n  (compression\n    (algorithm zstd)\n    (level 3)\n    (original-size 1048576)\n    (compressed-size 524288)\n    (ratio 0.5)))")))
  (section
    "Compression Algorithms"
    (subsection
      "Supported Algorithms"
      (code scheme "(define compression-algorithms\n  `((zstd . ((extension . \"zst\")\n             (levels . (1 3 9 19))\n             (default-level . 3)\n             (dictionary . #t)))\n    (lz4 . ((extension . \"lz4\")\n            (levels . (1 9))\n            (default-level . 1)\n            (dictionary . #f)))\n    (gzip . ((extension . \"gz\")\n             (levels . (1 6 9))\n             (default-level . 6)\n             (dictionary . #f)))\n    (none . ((extension . #f)\n             (levels . ())\n             (default-level . #f)\n             (dictionary . #f)))))"))
    (subsection
      "Algorithm Selection"
      (code scheme "(define (select-compression-algorithm content-type size)\n  \"Select best algorithm for content\"\n  (cond\n    ;; Already compressed formats\n    ((member content-type '(\"image/jpeg\" \"image/png\" \"video/mp4\"\n                           \"application/zip\" \"application/gzip\"))\n     'none)\n    ;; Small objects - overhead not worth it\n    ((< size 1024)\n     'none)\n    ;; Text and code - zstd with dictionary\n    ((member content-type '(\"text/plain\" \"text/html\" \"application/json\"\n                           \"application/javascript\" \"text/x-scheme\"))\n     'zstd)\n    ;; Binary data - lz4 for speed\n    ((string-prefix? \"application/\" content-type)\n     'lz4)\n    ;; Default\n    (else 'zstd)))"))
    (subsection
      "Zstd Dictionaries"
      (code scheme ";; Train dictionary on sample data\n(define (train-dictionary samples dict-size)\n  \"Train zstd dictionary from sample data\"\n  (zstd-train-dictionary samples dict-size))\n\n;; Content-type specific dictionaries\n(define dictionaries\n  `((scheme . ,(load-dictionary \"scheme.dict\"))\n    (json . ,(load-dictionary \"json.dict\"))\n    (markdown . ,(load-dictionary \"markdown.dict\"))))\n\n(define (compress-with-dictionary data content-type)\n  (let ((dict (assoc-ref dictionaries content-type)))\n    (if dict\n        (zstd-compress-with-dict data dict)\n        (zstd-compress data))))")))
  (section
    "Compression Operations"
    (subsection
      "Transparent Compression"
      (code scheme "(define (cas-put-compressed data)\n  \"Store data with transparent compression\"\n  (let ((hash (content-hash data))  ; Hash uncompressed\n         (algorithm (select-compression-algorithm\n                     (detect-content-type data)\n                     (bytevector-length data)))\n         (stored (if (eq? algorithm 'none)\n                     data\n                     (compress algorithm data))))\n    ;; Store compressed, index by uncompressed hash\n    (storage-put hash stored)\n    ;; Record compression metadata\n    (soup-put hash\n      compression: `((algorithm . ,algorithm)\n                     (original-size . ,(bytevector-length data))\n                     (compressed-size . ,(bytevector-length stored))))\n    hash))\n\n(define (cas-get-decompressed hash)\n  \"Retrieve and decompress data\"\n  (let ((stored (storage-get hash))\n         (meta (soup-get hash))\n         (algorithm (assoc-ref (assoc-ref meta 'compression) 'algorithm)))\n    (if (or (not algorithm) (eq? algorithm 'none))\n        stored\n        (decompress algorithm stored))))"))
    (subsection
      "Batch Compression"
      (code scheme "(define (compress-batch objects)\n  \"Compress multiple objects efficiently\"\n  ;; Group by content type for dictionary efficiency\n  (let ((groups (group-by detect-content-type objects)))\n    (append-map\n      (lambda (group)\n        (let ((content-type (car group))\n              (items (cdr group)))\n          (map (lambda (obj)\n                 (compress-with-dictionary obj content-type))\n               items)))\n      groups)))"))
    (subsection
      "Recompression"
      (code scheme "(define (recompress-object hash new-algorithm new-level)\n  \"Recompress object with different settings\"\n  (let* ((data (cas-get-decompressed hash))\n         (new-compressed (compress new-algorithm data new-level)))\n    (storage-put hash new-compressed)\n    (soup-update hash\n      compression: `((algorithm . ,new-algorithm)\n                     (level . ,new-level)\n                     (original-size . ,(bytevector-length data))\n                     (compressed-size . ,(bytevector-length new-compressed))))\n    (audit-append action: 'recompressed\n                  hash: hash\n                  algorithm: new-algorithm)))")))
  (section
    "Deduplication"
    (subsection
      "Content-Based Deduplication"
      (code scheme ";; Content addressing provides automatic deduplication\n(define (store-deduplicated data)\n  (let ((hash (content-hash data)))\n    (if (cas-exists? hash)\n        (begin\n          ;; Increment reference count\n          (soup-update hash ref-count: (+ 1 (soup-ref-count hash)))\n          (audit-append action: 'deduplicated hash: hash)\n          hash)\n        (cas-put data))))"))
    (subsection
      "Block-Level Deduplication"
      (code scheme ";; Split large objects into blocks\n(define block-size 65536)  ; 64KB\n\n(define (chunk-object data)\n  \"Split object into content-defined chunks\"\n  (let ((chunks '())\n        (pos 0))\n    (while (< pos (bytevector-length data))\n      (let ((boundary (find-chunk-boundary data pos)))\n        (set! chunks (cons (subbytevector data pos boundary) chunks))\n        (set! pos boundary)))\n    (reverse chunks)))\n\n;; Content-defined chunking (Rabin fingerprint)\n(define (find-chunk-boundary data start)\n  \"Find chunk boundary using rolling hash\"\n  (let ((min-size 4096)\n        (max-size 131072)\n        (mask #x1FFF))  ; Average 8KB chunks\n    (let loop ((pos (+ start min-size)))\n      (cond\n        ((>= pos (min (+ start max-size) (bytevector-length data)))\n         pos)\n        ((= (bitwise-and (rabin-hash data pos) mask) 0)\n         pos)\n        (else (loop (+ pos 1)))))))"))
    (subsection
      "Chunk Storage"
      (code scheme "(define (store-chunked data)\n  \"Store large object as deduplicated chunks\"\n  (let ((chunks (chunk-object data))\n         (chunk-hashes (map (lambda (chunk)\n                              (store-deduplicated chunk))\n                            chunks)))\n    ;; Store manifest\n    (let ((manifest `(chunked-object\n                      (chunks ,chunk-hashes)\n                      (total-size ,(bytevector-length data))\n                      (chunk-count ,(length chunks)))))\n      (cas-put (serialize manifest)))))\n\n(define (retrieve-chunked manifest-hash)\n  \"Reassemble chunked object\"\n  (let ((manifest (deserialize (cas-get manifest-hash)))\n         (chunks (map cas-get (assoc-ref manifest 'chunks))))\n    (bytevector-concatenate chunks)))"))
    (subsection
      "Deduplication Statistics"
      (code scheme "(define (deduplication-stats)\n  \"Calculate deduplication effectiveness\"\n  (let* ((objects (soup-query type: 'any))\n         (logical-size (sum (map soup-original-size objects)))\n         (physical-size (sum (map soup-compressed-size\n                                  (delete-duplicates objects hash=?)))))\n    `((logical-size . ,logical-size)\n      (physical-size . ,physical-size)\n      (dedup-ratio . ,(/ logical-size physical-size))\n      (space-saved . ,(- logical-size physical-size)))))")))
  (section
    "Delta Compression"
    (subsection
      "Version Deltas"
      (code scheme "(define (store-delta base-hash new-data)\n  \"Store object as delta from base\"\n  (let ((base-data (cas-get base-hash))\n         (delta (compute-delta base-data new-data))\n         (new-hash (content-hash new-data)))\n    (if (< (bytevector-length delta)\n           ( 0.5 (bytevector-length new-data)))\n        ;; Delta is worthwhile\n        (begin\n          (storage-put new-hash delta)\n          (soup-put new-hash\n            delta: `((base . ,base-hash)\n                     (type . xdelta)))\n          new-hash)\n        ;; Store full object\n        (cas-put new-data))))\n\n(define (retrieve-delta hash)\n  \"Reconstruct object from delta\"\n  (let ((meta (soup-get hash)))\n    (if (assoc-ref meta 'delta)\n        (let* ((base-hash (assoc-ref (assoc-ref meta 'delta) 'base))\n               (base-data (cas-get base-hash))\n               (delta (storage-get hash)))\n          (apply-delta base-data delta))\n        (storage-get hash))))"))
    (subsection
      "Delta Chains"
      (code scheme ";; Limit delta chain depth\n(define max-delta-depth 10\n\n(define (delta-chain-depth hash)\n  \"Calculate depth of delta chain\"\n  (let ((meta (soup-get hash)))\n    (if (assoc-ref meta 'delta)\n        (+ 1 (delta-chain-depth (assoc-ref (assoc-ref meta 'delta) 'base)))\n        0)))\n\n(define (should-store-delta? base-hash)\n  \"Check if delta storage is appropriate\"\n  (< (delta-chain-depth base-hash) max-delta-depth))")))
  (section
    "Archive Compression"
    (subsection
      "Sealed Archive Format"
      (code scheme ";; RFC-018 integration\n(define (create-compressed-archive objects)\n  \"Create compressed sealed archive\"\n  (let* ((serialized (serialize-objects objects))\n         (compressed (zstd-compress serialized 19))  ; Max compression\n         (encrypted (age-encrypt compressed recipients)))\n    (cas-put encrypted)))"))
    (subsection
      "Streaming Compression"
      (code scheme "(define (stream-compress input-port output-port algorithm)\n  \"Stream compression for large files\"\n  (let ((ctx (compression-context-create algorithm)))\n    (let loop ()\n      (let ((chunk (read-bytevector chunk-size input-port)))\n        (unless (eof-object? chunk)\n          (write-bytevector (compress-chunk ctx chunk) output-port)\n          (loop))))\n    (write-bytevector (compress-finish ctx) output-port)))")))
  (section
    "Performance Optimization"
    (subsection
      "Compression Cache"
      (code scheme "(define compression-cache (make-lru-cache 1000))\n\n(define (cached-decompress hash)\n  \"Cache decompressed data for frequent access\"\n  (or (lru-get compression-cache hash)\n      (let ((data (cas-get-decompressed hash)))\n        (lru-put! compression-cache hash data)\n        data)))"))
    (subsection
      "Parallel Compression"
      (code scheme "(define (parallel-compress objects num-threads)\n  \"Compress multiple objects in parallel\"\n  (let ((work-queue (make-channel))\n        (results (make-channel)))\n    ;; Start workers\n    (do ((i 0 (+ i 1)))\n        ((= i num-threads))\n      (thread-start!\n        (make-thread\n          (lambda ()\n            (let loop ()\n              (let ((obj (channel-get! work-queue)))\n                (when obj\n                  (channel-put! results (compress-object obj))\n                  (loop))))))))\n    ;; Queue work\n    (for-each (lambda (obj) (channel-put! work-queue obj)) objects)\n    ;; Collect results\n    (map (lambda (_) (channel-get! results)) objects)))"))
    (subsection
      "Adaptive Compression"
      (code scheme "(define (adaptive-compress data)\n  \"Select compression based on content analysis\"\n  (let* ((sample (subbytevector data 0 (min 4096 (bytevector-length data))))\n         (entropy (calculate-entropy sample)))\n    (cond\n      ;; High entropy - already compressed or encrypted\n      ((> entropy 7.9) 'none)\n      ;; Low entropy - highly compressible\n      ((< entropy 4.0) (values 'zstd 19))\n      ;; Medium entropy - balanced\n      (else (values 'zstd 3)))))")))
  (section
    "Integrity"
    (subsection
      "Verification"
      (code scheme "(define (verify-compressed-object hash)\n  \"Verify compressed object integrity\"\n  (let* ((stored (storage-get hash))\n         (meta (soup-get hash))\n         (decompressed (decompress (assoc-ref meta 'algorithm) stored))\n         (computed-hash (content-hash decompressed)))\n    (equal? hash computed-hash)))"))
    (subsection
      "Corruption Recovery"
      (code scheme "(define (recover-compressed hash)\n  \"Attempt to recover corrupted compressed object\"\n  ;; Try partial decompression\n  (let ((partial (decompress-partial hash)))\n    (when partial\n      (audit-append action: 'partial-recovery hash: hash)\n      partial))\n\n  ;; Fetch from replica\n  (let ((replica-data (fetch-from-replica hash)))\n    (when replica-data\n      (storage-put hash replica-data)\n      replica-data)))")))
  (section
    "References"
    (p "1. [Zstandard](https://github.com/facebook/zstd) - Facebook's compression algorithm 2. [Content-Defined Chunking](https://restic.net/blog/2015-09-12/restic-foundation1-cdc/) - Restic blog 3. [RFC-018: Sealed Archive Format](rfc-018-sealed-archive.html) 4. [RFC-020: Content-Addressed Storage](rfc-020-content-addressed-storage.html)"))
  (section
    "Changelog"
    (list
      (item "2026-01-07")
      (item "Initial draft"))))

