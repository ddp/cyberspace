;; Auto-converted from Markdown
;; Review and edit as needed

(rfc
  (number 31)
  (title "Monitoring and Observability")
  (section
    "Abstract"
    (p "This RFC specifies monitoring and observability for the Library of Cyberspace: how vaults expose metrics, traces, and logs for operational visibility while maintaining privacy and security. Observability data is itself content-addressed and auditable."))
  (section
    "Motivation"
    (p "Operating distributed systems requires visibility:")
    (p "- Health - Is the vault functioning correctly? - Performance - How fast are operations? - Capacity - How much storage remains? - Errors - What's failing and why? - Security - Who's accessing what?")
    (p "But observability must not compromise:")
    (p "- Privacy - No sensitive data in metrics - Security - Metrics don't leak capabilities - Performance - Minimal overhead - Storage - Observability data is bounded"))
  (section
    "Metrics"
    (subsection
      "Core Metrics"
      (code scheme "(define vault-metrics\n  '(;; Storage\n    (storage.used.bytes gauge \"Total bytes used\")\n    (storage.available.bytes gauge \"Bytes available\")\n    (storage.objects.count gauge \"Number of objects\")\n\n    ;; Operations\n    (cas.put.count counter \"CAS put operations\")\n    (cas.put.bytes counter \"Bytes written\")\n    (cas.put.duration histogram \"Put latency\")\n    (cas.get.count counter \"CAS get operations\")\n    (cas.get.bytes counter \"Bytes read\")\n    (cas.get.duration histogram \"Get latency\")\n\n    ;; Soup\n    (soup.queries.count counter \"Soup queries\")\n    (soup.queries.duration histogram \"Query latency\")\n    (soup.index.size.bytes gauge \"Index size\")\n\n    ;; Network\n    (network.connections.active gauge \"Active connections\")\n    (network.bytes.sent counter \"Bytes sent\")\n    (network.bytes.received counter \"Bytes received\")\n\n    ;; Replication\n    (replication.lag.seconds gauge \"Replication lag\")\n    (replication.objects.pending gauge \"Objects pending sync\")\n\n    ;; Errors\n    (errors.total counter \"Total errors\" labels: (type))\n    (errors.rate gauge \"Error rate per second\")))"))
    (subsection
      "Metric Collection"
      (code scheme "(define metrics-registry (make-hash-table))\n\n(define (register-metric name type help #!key labels)\n  (hash-table-set! metrics-registry name\n    `((type . ,type)\n      (help . ,help)\n      (labels . ,labels)\n      (value . ,(case type\n                  ((counter) 0)\n                  ((gauge) 0)\n                  ((histogram) (make-histogram-buckets)))))))\n\n(define (metric-inc! name #!key (delta 1) labels)\n  (let ((metric (hash-table-ref metrics-registry name)))\n    (case (assoc-ref metric 'type)\n      ((counter gauge)\n       (set! (assoc-ref metric 'value)\n             (+ (assoc-ref metric 'value) delta))))))\n\n(define (metric-set! name value #!key labels)\n  (let ((metric (hash-table-ref metrics-registry name)))\n    (set! (assoc-ref metric 'value) value)))\n\n(define (metric-observe! name value #!key labels)\n  (let ((metric (hash-table-ref metrics-registry name)))\n    (histogram-observe! (assoc-ref metric 'value) value)))"))
    (subsection
      "Histogram Buckets"
      (code scheme "(define (make-histogram-buckets)\n  \"Default latency buckets in milliseconds\"\n  (let ((buckets '(1 5 10 25 50 100 250 500 1000 2500 5000 10000)))\n    (map (lambda (b) (cons b 0)) buckets)))\n\n(define (histogram-observe! histogram value)\n  (for-each (lambda (bucket)\n              (when (<= value (car bucket))\n                (set-cdr! bucket (+ (cdr bucket) 1))))\n            histogram))")))
  (section
    "Tracing"
    (subsection
      "Trace Structure"
      (code scheme "(define (make-trace operation)\n  `(trace\n    (trace-id ,(generate-trace-id))\n    (span-id ,(generate-span-id))\n    (parent-span-id #f)\n    (operation ,operation)\n    (start-time ,(current-time-ns))\n    (end-time #f)\n    (status pending)\n    (attributes ())\n    (events ())))\n\n(define (trace-start! trace)\n  (set! (assoc-ref trace 'start-time) (current-time-ns))\n  trace)\n\n(define (trace-end! trace status)\n  (set! (assoc-ref trace 'end-time) (current-time-ns))\n  (set! (assoc-ref trace 'status) status)\n  (record-trace! trace))"))
    (subsection
      "Span Context"
      (code scheme "(define current-trace (make-parameter #f))\n(define current-span (make-parameter #f))\n\n(define (with-span operation proc)\n  \"Execute proc within a traced span\"\n  (let* ((parent (current-span))\n         (span (make-span operation (and parent (span-id parent)))))\n    (parameterize ((current-span span))\n      (span-start! span)\n      (guard (ex\n              (else\n               (span-error! span ex)\n               (span-end! span 'error)\n               (raise ex)))\n        (let ((result (proc)))\n          (span-end! span 'ok)\n          result)))))\n\n;; Example usage\n(define (traced-cas-get hash)\n  (with-span \"cas.get\"\n    (lambda ()\n      (span-set-attribute! \"hash\" hash)\n      (cas-get hash))))"))
    (subsection
      "Distributed Tracing"
      (code scheme ";; Propagate trace context across vault boundaries\n(define (inject-trace-context headers)\n  \"Inject trace context into outgoing request\"\n  (let ((span (current-span)))\n    (when span\n      (hash-table-set! headers \"X-Trace-Id\" (span-trace-id span))\n      (hash-table-set! headers \"X-Span-Id\" (span-id span)))))\n\n(define (extract-trace-context headers)\n  \"Extract trace context from incoming request\"\n  (let ((trace-id (hash-table-ref headers \"X-Trace-Id\" #f))\n        (parent-span-id (hash-table-ref headers \"X-Span-Id\" #f)))\n    (when trace-id\n      (current-trace trace-id)\n      (make-span-with-parent parent-span-id))))")))
  (section
    "Logging"
    (subsection
      "Structured Logging"
      (code scheme "(define (log level message #!rest attributes)\n  \"Emit structured log entry\"\n  (let ((entry `((timestamp . ,(current-time-iso8601))\n                 (level . ,level)\n                 (message . ,message)\n                 (vault . ,(vault-id))\n                 (trace-id . ,(and (current-span) (span-trace-id (current-span))))\n                 ,@(plist->alist attributes))))\n    (emit-log entry)))\n\n(define (log-debug message . attrs) (apply log 'debug message attrs))\n(define (log-info message . attrs) (apply log 'info message attrs))\n(define (log-warn message . attrs) (apply log 'warn message attrs))\n(define (log-error message . attrs) (apply log 'error message attrs))\n\n;; Example\n(log-info \"Object stored\"\n          'hash hash\n          'size (bytevector-length data)\n          'duration-ms elapsed)"))
    (subsection
      "Log Levels"
      (code scheme "(define log-levels '((trace . 0) (debug . 1) (info . 2)\n                     (warn . 3) (error . 4) (fatal . 5)))\n\n(define current-log-level (make-parameter 'info))\n\n(define (log-enabled? level)\n  (>= (assoc-ref log-levels level)\n      (assoc-ref log-levels (current-log-level))))"))
    (subsection
      "Log Sinks"
      (code scheme ";; Multiple output destinations\n(define log-sinks '())\n\n(define (add-log-sink! sink)\n  (set! log-sinks (cons sink log-sinks)))\n\n(define (emit-log entry)\n  (when (log-enabled? (assoc-ref entry 'level))\n    (for-each (lambda (sink)\n                (sink-write sink entry))\n              log-sinks)))\n\n;; Sink implementations\n(define (make-file-sink path)\n  (lambda (entry)\n    (with-output-to-file path\n      (lambda () (write-json entry) (newline))\n      'append)))\n\n(define (make-soup-sink)\n  (lambda (entry)\n    (soup-put entry type: 'log-entry)))")))
  (section
    "Health Checks"
    (subsection
      "Health Endpoints"
      (code scheme "(define (health-check)\n  \"Comprehensive health check\"\n  ((status . ,(if (all-healthy?) 'healthy 'unhealthy))\n    (checks . ((storage . ,(check-storage))\n               (network . ,(check-network))\n               (replication . ,(check-replication))\n               (keys . ,(check-keys))))))\n\n(define (check-storage)\n  ((status . ,(if (storage-accessible?) 'healthy 'unhealthy))\n    (used . ,(storage-used))\n    (available . ,(storage-available))\n    (percent . ,(storage-percent-used))))\n\n(define (check-network)\n  ((status . ,(if (network-healthy?) 'healthy 'unhealthy))\n    (peers . ,(connected-peer-count))\n    (latency-ms . ,(average-peer-latency))))\n\n(define (check-replication)\n  ((status . ,(if (replication-healthy?) 'healthy 'unhealthy))\n    (lag-seconds . ,(replication-lag))\n    (pending . ,(pending-replication-count))))"))
    (subsection
      "Readiness vs Liveness"
      (code scheme ";; Liveness: is the process running?\n(define (liveness-check)\n  '((status . alive)))\n\n;; Readiness: can we serve requests?\n(define (readiness-check)\n  (if (and (storage-accessible?)\n           (keys-available?)\n           (not (vault-readonly?)))\n      '((status . ready))\n      '((status . not-ready))))")))
  (section
    "Alerting"
    (subsection
      "Alert Rules"
      (code scheme "(define alert-rules\n  `((storage-critical\n     (condition (> (metric-value 'storage.percent.used) 95))\n     (severity critical)\n     (message \"Storage critically low\"))\n\n    (storage-warning\n     (condition (> (metric-value 'storage.percent.used) 80))\n     (severity warning)\n     (message \"Storage running low\"))\n\n    (error-rate-high\n     (condition (> (metric-value 'errors.rate) 10))\n     (severity warning)\n     (message \"High error rate detected\"))\n\n    (replication-lag\n     (condition (> (metric-value 'replication.lag.seconds) 300))\n     (severity warning)\n     (message \"Replication lag exceeds 5 minutes\"))\n\n    (peer-disconnected\n     (condition (< (metric-value 'network.peers.connected) 1))\n     (severity critical)\n     (message \"No peers connected\"))))"))
    (subsection
      "Alert Evaluation"
      (code scheme "(define (evaluate-alerts)\n  \"Check all alert conditions\"\n  (filter-map\n    (lambda (rule)\n      (when (eval-condition (assoc-ref rule 'condition))\n        (fire-alert rule)))\n    alert-rules))\n\n(define (fire-alert rule)\n  (let ((alert `((name . ,(car rule))\n                 (severity . ,(assoc-ref (cdr rule) 'severity))\n                 (message . ,(assoc-ref (cdr rule) 'message))\n                 (timestamp . ,(current-time)))))\n    (audit-append action: 'alert-fired alert: alert)\n    (notify-alert alert)\n    alert))")))
  (section
    "Dashboards"
    (subsection
      "Metric Export"
      (code scheme ";; Prometheus format\n(define (export-prometheus)\n  (with-output-to-string\n    (lambda ()\n      (for-each\n        (lambda (metric)\n          (let ((name (car metric))\n                (data (cdr metric)))\n            (format #t \"# HELP ~a ~a~%\" name (assoc-ref data 'help))\n            (format #t \"# TYPE ~a ~a~%\" name (assoc-ref data 'type))\n            (format #t \"~a ~a~%\" name (assoc-ref data 'value))))\n        (hash-table->alist metrics-registry)))))"))
    (subsection
      "Status Page"
      (code scheme "(define (status-page)\n  \"Generate human-readable status\"\n  `(vault-status\n    (health . ,(health-check))\n    (uptime . ,(vault-uptime))\n    (version . ,(vault-version))\n    (metrics . ((storage . ,(storage-metrics))\n                (operations . ,(operation-metrics))\n                (network . ,(network-metrics))))\n    (recent-errors . ,(recent-errors 10))))")))
  (section
    "Privacy"
    (subsection
      "Metric Sanitization"
      (code scheme ";; Never expose sensitive data in metrics\n(define (sanitize-metric-labels labels)\n  (map (lambda (label)\n         (case (car label)\n           ((hash) (cons 'hash \"[REDACTED]\"))\n           ((principal) (cons 'principal (hash-principal (cdr label))))\n           (else label)))\n       labels))\n\n(define (safe-metric name value #!key labels)\n  (metric-set! name value labels: (sanitize-metric-labels labels)))"))
    (subsection
      "Aggregate Metrics Only"
      (code scheme ";; Expose only aggregates, not individual operations\n(define (operation-metrics)\n  `((total-operations . ,(metric-value 'cas.operations.total))\n    (operations-per-second . ,(metric-value 'cas.operations.rate))\n    (average-latency-ms . ,(metric-value 'cas.latency.average))\n    (p99-latency-ms . ,(metric-value 'cas.latency.p99))))")))
  (section
    "Storage"
    (subsection
      "Metric Retention"
      (code scheme ";; Metrics stored in soup with TTL\n(define metric-retention ( 30 24 3600))  ; 30 days\n\n(define (store-metric-snapshot)\n  \"Periodic metric snapshot\"\n  (let ((snapshot `((timestamp . ,(current-time))\n                    (metrics . ,(export-all-metrics)))))\n    (soup-put snapshot\n      type: 'metric-snapshot\n      ttl: metric-retention)))\n\n(define (gc-old-metrics)\n  \"Remove expired metric snapshots\"\n  (let ((expired (soup-query type: 'metric-snapshot\n                             timestamp: (< (- (current-time) metric-retention*)))))\n    (for-each soup-delete! expired)))"))
    (subsection
      "Trace Sampling"
      (code scheme ";; Sample traces to control storage\n(define trace-sample-rate 0.1)  ; 10%\n\n(define (should-sample-trace?)\n  (< (random 1.0) trace-sample-rate))\n\n(define (record-trace! trace)\n  (when (or (trace-has-error? trace)\n            (should-sample-trace?))\n    (soup-put trace type: 'trace)))")))
  (section
    "References"
    (p "1. [OpenTelemetry](https://opentelemetry.io/) - Observability framework 2. [Prometheus](https://prometheus.io/) - Monitoring system 3. [RFC-003: Cryptographic Audit Trail](rfc-003-audit-trail.html) 4. [RFC-028: Error Handling](rfc-028-error-handling.html)"))
  (section
    "Changelog"
    (p "- 2026-01-07 - Initial draft")))

