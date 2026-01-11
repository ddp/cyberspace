;; Auto-converted from Markdown
;; Review and edit as needed

(rfc
  (number 33)
  (title "Schema Evolution")
  (section
    "Abstract"
    (p "This RFC specifies schema evolution for the Library of Cyberspace: how soup metadata schemas change over time while maintaining backward compatibility, migration paths, and query consistency. Schemas are themselves content-addressed objects."))
  (section
    "Motivation"
    (p "Data outlives code:")
    (p "- Long-term preservation - Data must remain readable for centuries - Software updates - New versions need new fields - Federation - Different vaults may have different schema versions - Rollback - Must handle downgrades gracefully")
    (p "Schema evolution must be:")
    (p "- Non-breaking - Old data remains accessible - Bidirectional - Upgrade and downgrade paths - Explicit - Changes documented and versioned - Verifiable - Schema validation at boundaries"))
  (section
    "Schema Model"
    (subsection
      "Schema Definition"
      (code scheme "(define-schema 'document\n  (version 1)\n  (fields\n    (hash (type string) (required #t) (indexed #t))\n    (name (type string) (required #t))\n    (content-type (type string) (required #t))\n    (size (type integer) (required #t))\n    (created (type timestamp) (required #t))\n    (modified (type timestamp) (required #f))\n    (author (type principal) (required #f))\n    (tags (type (list string)) (required #f) (default '()))))"))
    (subsection
      "Schema as Content-Addressed Object"
      (code scheme ";; Schemas are soup objects\n(soup-object\n  (hash \"sha256:schema-hash...\")\n  (type schema)\n  (name document)\n  (version 1)\n  (fields ...)\n  (created \"2026-01-01\"))\n\n;; Reference schema by hash for reproducibility\n(define (validate-against-schema obj schema-hash)\n  (let ((schema (soup-get schema-hash)))\n    (validate-object obj schema)))"))
    (subsection
      "Schema Registry"
      (code scheme "(define schema-registry (make-hash-table))\n\n(define (register-schema! schema)\n  (let* ((name (schema-name schema))\n         (version (schema-version schema))\n         (hash (soup-put schema type: 'schema)))\n    (hash-table-set! schema-registry (cons name version) hash)\n    (audit-append action: 'schema-registered\n                  name: name\n                  version: version\n                  hash: hash)\n    hash))\n\n(define (get-schema name #!optional version)\n  \"Get schema by name and optional version\"\n  (if version\n      (soup-get (hash-table-ref schema-registry (cons name version)))\n      (get-latest-schema name)))")))
  (section
    "Evolution Rules"
    (subsection
      "Compatible Changes"
      (code scheme ";; These changes are backward compatible\n(define compatible-changes\n  '(add-optional-field      ; New field with default\n    add-index               ; New index on existing field\n    widen-type              ; integer -> number\n    relax-constraint        ; required -> optional\n    add-enum-value))        ; Extend enumeration\n\n(define (change-compatible? old-schema new-schema)\n  \"Check if schema change is backward compatible\"\n  (let ((changes (diff-schemas old-schema new-schema)))\n    (every compatible-change? changes)))"))
    (subsection
      "Breaking Changes"
      (code scheme ";; These changes require migration\n(define breaking-changes\n  '(remove-field            ; Field no longer exists\n    add-required-field      ; New required field without default\n    narrow-type             ; number -> integer\n    tighten-constraint      ; optional -> required\n    remove-enum-value       ; Shrink enumeration\n    rename-field))          ; Field name changed\n\n(define (requires-migration? old-schema new-schema)\n  \"Check if migration needed\"\n  (let ((changes (diff-schemas old-schema new-schema)))\n    (any breaking-change? changes)))")))
  (section
    "Version Management"
    (subsection
      "Semantic Versioning"
      (code scheme ";; Schema versions follow semver\n(define (schema-version-compare v1 v2)\n  (let ((major1 (version-major v1)) (major2 (version-major v2))\n        (minor1 (version-minor v1)) (minor2 (version-minor v2))\n        (patch1 (version-patch v1)) (patch2 (version-patch v2)))\n    (cond\n      ((not (= major1 major2)) (- major1 major2))\n      ((not (= minor1 minor2)) (- minor1 minor2))\n      (else (- patch1 patch2)))))\n\n;; Major: breaking changes\n;; Minor: compatible additions\n;; Patch: documentation/fixes"))
    (subsection
      "Version History"
      (code scheme "(define (schema-history name)\n  \"Get all versions of a schema\"\n  (soup-query type: 'schema\n              name: name\n              order-by: '((version desc))))\n\n(define (schema-lineage name version)\n  \"Get evolution path to current version\"\n  (let ((schema (get-schema name version)))\n    (if (schema-parent schema)\n        (cons schema (schema-lineage name (schema-parent-version schema)))\n        (list schema))))")))
  (section
    "Migration"
    (subsection
      "Migration Definition"
      (code scheme "(define-migration 'document-v1-to-v2\n  (from-schema 'document (version 1))\n  (to-schema 'document (version 2))\n  (up (lambda (obj)\n        ;; Add new field with default\n        (assoc-set obj 'visibility 'private)))\n  (down (lambda (obj)\n          ;; Remove new field\n          (assoc-remove obj 'visibility))))"))
    (subsection
      "Migration Execution"
      (code scheme "(define (migrate-object obj from-version to-version)\n  \"Migrate object between schema versions\"\n  (let ((migrations (find-migration-path from-version to-version)))\n    (fold (lambda (migration obj)\n            ((migration-up migration) obj))\n          obj\n          migrations)))\n\n(define (find-migration-path from to)\n  \"Find sequence of migrations between versions\"\n  (let ((direction (if (> to from) 'up 'down)))\n    (filter (lambda (m)\n              (and (eq? (migration-direction m) direction)\n                   (version-in-range? (migration-from m) from to)))\n            (all-migrations))))"))
    (subsection
      "Lazy Migration"
      (code scheme ";; Migrate on read, not on upgrade\n(define (soup-get-migrated hash)\n  \"Get object, migrating if necessary\"\n  (let ((obj (soup-get-raw hash))\n         (obj-version (object-schema-version obj))\n         (current-version (current-schema-version (object-type obj))))\n    (if (= obj-version current-version)\n        obj\n        (let ((migrated (migrate-object obj obj-version current-version)))\n          ;; Optionally persist migrated version\n          (when persist-migrations*\n            (soup-put-raw migrated))\n          migrated))))"))
    (subsection
      "Batch Migration"
      (code scheme "(define (batch-migrate schema-name from-version to-version)\n  \"Migrate all objects of a schema\"\n  (let ((objects (soup-query type: schema-name\n                             schema-version: from-version)))\n    (for-each (lambda (obj)\n                (let ((migrated (migrate-object obj from-version to-version)))\n                  (soup-update (object-hash obj) migrated)\n                  (audit-append action: 'object-migrated\n                                hash: (object-hash obj)\n                                from: from-version\n                                to: to-version)))\n              objects)))")))
  (section
    "Validation"
    (subsection
      "Schema Validation"
      (code scheme "(define (validate-object obj schema)\n  \"Validate object against schema\"\n  (let ((errors '()))\n    ;; Check required fields\n    (for-each (lambda (field)\n                (when (and (field-required? field)\n                           (not (assoc-ref obj (field-name field))))\n                  (set! errors (cons (missing-required ,(field-name field))\n                                    errors))))\n              (schema-fields schema))\n\n    ;; Check field types\n    (for-each (lambda (pair)\n                (let* ((name (car pair))\n                       (value (cdr pair))\n                       (field (schema-field schema name)))\n                  (when (and field (not (type-matches? value (field-type field))))\n                    (set! errors (cons (type-mismatch ,name) errors)))))\n              obj)\n\n    (if (null? errors)\n        (result-ok obj)\n        (result-err errors))))"))
    (subsection
      "Validation Modes"
      (code scheme "(define validation-mode (make-parameter 'strict))\n\n(define (validate-with-mode obj schema)\n  (case (validation-mode)\n    ((strict)\n     ;; All fields must match schema\n     (validate-object obj schema))\n    ((permissive)\n     ;; Extra fields allowed\n     (validate-required-fields obj schema))\n    ((warn)\n     ;; Log warnings but don't fail\n     (let ((result (validate-object obj schema)))\n       (when (result-err? result)\n         (log-warn \"Validation errors\" errors: (result-error result)))\n       (result-ok obj)))))")))
  (section
    "Federation Compatibility"
    (subsection
      "Schema Negotiation"
      (code scheme "(define (negotiate-schema peer schema-name)\n  \"Negotiate compatible schema version with peer\"\n  (let* ((local-versions (local-schema-versions schema-name))\n         (peer-versions (request-schema-versions peer schema-name))\n         (compatible (intersection local-versions peer-versions)))\n    (if (null? compatible)\n        (error 'no-compatible-schema)\n        (max compatible))))\n\n(define (sync-with-schema-version peer schema-name version)\n  \"Sync objects using negotiated schema version\"\n  (for-each (lambda (obj)\n              (let ((converted (convert-to-version obj version)))\n                (send-object peer converted)))\n            (objects-to-sync schema-name)))"))
    (subsection
      "Cross-Version Queries"
      (code scheme "(define (query-with-version-tolerance query)\n  \"Query that handles mixed schema versions\"\n  (let* ((results (soup-query-raw query))\n         (current-version (current-schema-version (query-type query))))\n    (map (lambda (obj)\n           (if (= (object-schema-version obj) current-version)\n               obj\n               (migrate-object obj (object-schema-version obj) current-version)))\n         results)))")))
  (section
    "Schema Introspection"
    (subsection
      "Schema Queries"
      (code scheme ";; What schemas exist?\n(soup-query type: 'schema)\n\n;; What versions of a schema?\n(soup-query type: 'schema name: 'document)\n\n;; What fields in a schema?\n(schema-fields (get-schema 'document 2))\n\n;; Schema dependency graph\n(define (schema-dependencies schema)\n  (filter-map (lambda (field)\n                (when (schema-reference? (field-type field))\n                  (field-type-target field)))\n              (schema-fields schema)))"))
    (subsection
      "Schema Documentation"
      (code scheme "(define-schema 'document\n  (version 2)\n  (description \"A document stored in the vault\")\n  (fields\n    (hash\n      (type string)\n      (required #t)\n      (indexed #t)\n      (description \"Content-addressed hash of document\"))\n    (name\n      (type string)\n      (required #t)\n      (description \"Human-readable document name\")\n      (example \"RFC-033-schema-evolution.md\"))))")))
  (section
    "Default Values"
    (subsection
      "Static Defaults"
      (code scheme "(define-schema 'document\n  (version 2)\n  (fields\n    (visibility\n      (type enum)\n      (values (public private restricted))\n      (default 'private))\n    (tags\n      (type (list string))\n      (default '()))))"))
    (subsection
      "Computed Defaults"
      (code scheme "(define-schema 'document\n  (version 2)\n  (fields\n    (created\n      (type timestamp)\n      (default (current-time)))\n    (id\n      (type string)\n      (default (generate-uuid)))))"))
    (subsection
      "Migration Defaults"
      (code scheme ";; Default for objects migrated from v1 to v2\n(define-migration 'document-v1-to-v2\n  (defaults\n    (visibility (lambda (obj)\n                  ;; Infer from existing data\n                  (if (assoc-ref obj 'public)\n                      'public\n                      'private)))))")))
  (section
    "Security Considerations"
    (subsection
      "Schema Tampering"
      (code scheme ";; Schemas are content-addressed - tampering detectable\n(define (verify-schema-integrity schema-hash)\n  (let* ((schema (soup-get schema-hash))\n         (computed-hash (content-hash (serialize schema))))\n    (equal? schema-hash computed-hash)))"))
    (subsection
      "Migration Authorization"
      (code scheme ";; Migrations require capability\n(spki-cert\n  (issuer vault-admin)\n  (subject schema-admin)\n  (capability\n    (action migrate-schema)\n    (object (schema 'document)))\n  (validity (not-after \"2027-01-01\")))")))
  (section
    "References"
    (p "1. [Protocol Buffers - Updating A Message Type](https://developers.google.com/protocol-buffers/docs/proto#updating) 2. [Avro Schema Evolution](https://avro.apache.org/docs/current/spec.html#Schema+Resolution) 3. [RFC-020: Content-Addressed Storage](rfc-020-content-addressed-storage.html) 4. [RFC-025: Query Language](rfc-025-query-language.html)"))
  (section
    "Changelog"
    (p "- 2026-01-07 - Initial draft")))

