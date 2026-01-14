;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 32)
  (title "Rate Limiting and Quotas")
  (section
    "Abstract"
    (p "This RFC specifies rate limiting and quotas for the Library of Cyberspace: how vaults protect themselves from abuse while ensuring fair access for legitimate users. Limits are capability-aware and auditable."))
  (section
    "Motivation"
    (p "Shared resources require protection:")
    (list
      (item "Denial of Service")
      (item "Malicious overload")
      (item "Resource exhaustion")
      (item "Runaway processes")
      (item "Fair sharing")
      (item "Equal access for all users")
      (item "Cost control")
      (item "Prevent unbounded consumption"))
    (p "Limits must be:")
    (list
      (item "Configurable")
      (item "Different limits for different principals")
      (item "Graceful")
      (item "Degrade smoothly, don't cliff")
      (item "Transparent")
      (item "Users know their limits")
      (item "Auditable")
      (item "All limiting decisions logged")))
  (section
    "Rate Limiting"
    (subsection
      "Token Bucket Algorithm"
      (code scheme "(define (make-token-bucket capacity fill-rate)\n  \"Create token bucket rate limiter\"\n  (let ((tokens capacity)\n        (last-fill (current-time-ms)))\n\n    (lambda (cost)\n      ;; Refill tokens based on elapsed time\n      (let ((now (current-time-ms))\n             (elapsed (- now last-fill))\n             (new-tokens (+ tokens ( fill-rate (/ elapsed 1000)))))\n        (set! tokens (min capacity new-tokens))\n        (set! last-fill now)\n\n        ;; Try to consume tokens\n        (if (>= tokens cost)\n            (begin\n              (set! tokens (- tokens cost))\n              #t)  ; Allowed\n            #f))))) ; Denied\n\n;; Example: 100 requests per second, burst of 200\n(define request-limiter (make-token-bucket 200 100))"))
    (subsection
      "Sliding Window"
      (code scheme "(define (make-sliding-window size interval)\n  \"Sliding window rate limiter\"\n  (let ((events (make-deque)))\n\n    (lambda ()\n      ;; Remove old events\n      (let ((cutoff (- (current-time-ms) interval)))\n        (while (and (not (deque-empty? events))\n                    (< (deque-front events) cutoff))\n          (deque-pop-front! events)))\n\n      ;; Check if under limit\n      (if (< (deque-length events) size)\n          (begin\n            (deque-push-back! events (current-time-ms))\n            #t)\n          #f))))"))
    (subsection
      "Leaky Bucket"
      (code scheme "(define (make-leaky-bucket capacity leak-rate)\n  \"Leaky bucket for smoothing bursts\"\n  (let ((level 0)\n        (last-leak (current-time-ms)))\n\n    (lambda (amount)\n      ;; Leak based on elapsed time\n      (let ((now (current-time-ms))\n             (elapsed (- now last-leak))\n             (leaked ( leak-rate (/ elapsed 1000))))\n        (set! level (max 0 (- level leaked)))\n        (set! last-leak now)\n\n        ;; Try to add to bucket\n        (if (<= (+ level amount) capacity)\n            (begin\n              (set! level (+ level amount))\n              #t)\n            #f)))))")))
  (section
    "Quota System"
    (subsection
      "Quota Types"
      (code scheme "(define quota-types\n  '((storage . ((unit . bytes)\n                (period . #f)          ; No reset\n                (default . 10737418240))) ; 10GB\n\n    (bandwidth . ((unit . bytes)\n                  (period . monthly)\n                  (default . 107374182400))) ; 100GB/month\n\n    (requests . ((unit . count)\n                 (period . daily)\n                 (default . 100000)))    ; 100k/day\n\n    (objects . ((unit . count)\n                (period . #f)\n                (default . 1000000)))))  ; 1M objects"))
    (subsection
      "Quota Tracking"
      (code scheme "(define principal-quotas (make-hash-table))\n\n(define (get-quota principal quota-type)\n  \"Get principal's quota for type\"\n  (let ((quotas (hash-table-ref principal-quotas principal '())))\n    (or (assoc-ref quotas quota-type)\n        (assoc-ref quota-types quota-type 'default))))\n\n(define (get-usage principal quota-type)\n  \"Get principal's current usage\"\n  (let ((period (quota-period quota-type)))\n    (soup-aggregate\n      where: (and (type: 'usage-record)\n                  (principal: principal)\n                  (quota-type: quota-type)\n                  (if period\n                      (timestamp: (> (period-start period)))\n                      #t))\n      aggregate: (sum 'amount))))\n\n(define (check-quota principal quota-type amount)\n  \"Check if operation would exceed quota\"\n  (let ((quota (get-quota principal quota-type))\n        (usage (get-usage principal quota-type)))\n    (<= (+ usage amount) quota)))"))
    (subsection
      "Quota Enforcement"
      (code scheme "(define (enforce-quota principal quota-type amount)\n  \"Enforce quota, raise error if exceeded\"\n  (unless (check-quota principal quota-type amount)\n    (let ((quota (get-quota principal quota-type))\n          (usage (get-usage principal quota-type)))\n      (audit-append action: 'quota-exceeded\n                    principal: principal\n                    quota-type: quota-type\n                    quota: quota\n                    usage: usage\n                    requested: amount)\n      (error 'quota-exceeded\n             ((type . ,quota-type)\n               (quota . ,quota)\n               (usage . ,usage)\n               (requested . ,amount))))))\n\n(define (record-usage principal quota-type amount)\n  \"Record quota usage\"\n  (soup-put\n    ((type . usage-record)\n      (principal . ,principal)\n      (quota-type . ,quota-type)\n      (amount . ,amount)\n      (timestamp . ,(current-time)))))")))
  (section
    "Principal-Based Limits"
    (subsection
      "Limit Tiers"
      (code scheme "(define limit-tiers\n  '((anonymous . ((requests-per-second . 10)\n                  (storage-bytes . 0)\n                  (bandwidth-bytes . 1073741824)))\n\n    (authenticated . ((requests-per-second . 100)\n                      (storage-bytes . 10737418240)\n                      (bandwidth-bytes . 107374182400)))\n\n    (premium . ((requests-per-second . 1000)\n                (storage-bytes . 1099511627776)\n                (bandwidth-bytes . 10995116277760)))\n\n    (admin . ((requests-per-second . #f)  ; Unlimited\n              (storage-bytes . #f)\n              (bandwidth-bytes . #f)))))\n\n(define (principal-tier principal)\n  \"Determine principal's limit tier\"\n  (cond\n    ((admin-principal? principal) 'admin)\n    ((premium-principal? principal) 'premium)\n    ((authenticated? principal) 'authenticated)\n    (else 'anonymous)))"))
    (subsection
      "Per-Principal Limiters"
      (code scheme "(define principal-limiters (make-hash-table))\n\n(define (get-limiter principal)\n  \"Get or create rate limiter for principal\"\n  (or (hash-table-ref principal-limiters principal #f)\n      (let ((tier (principal-tier principal))\n             (rps (assoc-ref (assoc-ref limit-tiers tier)\n                            'requests-per-second)))\n        (if rps\n            (let ((limiter (make-token-bucket ( rps 2) rps)))\n              (hash-table-set! principal-limiters principal limiter)\n              limiter)\n            (lambda (_) #t)))))  ; Unlimited\n\n(define (rate-limit-principal principal)\n  \"Apply rate limit to principal\"\n  (let ((limiter (get-limiter principal)))\n    (unless (limiter 1)\n      (audit-append action: 'rate-limited principal: principal)\n      (error 'rate-limited))))"))
    (subsection
      "Capability-Based Limits"
      (code scheme ";; Capabilities can include rate limits\n(spki-cert\n  (issuer vault-admin)\n  (subject api-client)\n  (capability\n    (action read)\n    (object vault-content)\n    (rate-limit\n      (requests-per-second 50)\n      (burst 100)))\n  (validity (not-after \"2027-01-01\")))\n\n(define (capability-rate-limit cap)\n  \"Extract rate limit from capability\"\n  (assoc-ref cap 'rate-limit))")))
  (section
    "Resource-Specific Limits"
    (subsection
      "Storage Limits"
      (code scheme "(define (enforce-storage-limit principal size)\n  \"Enforce storage quota before write\"\n  (let* ((quota (get-quota principal 'storage))\n         (used (principal-storage-used principal)))\n    (when (and quota (> (+ used size) quota))\n      (error 'storage-quota-exceeded\n             `((quota . ,quota)\n               (used . ,used)\n               (requested . ,size))))))\n\n(define (principal-storage-used principal)\n  \"Calculate principal's storage usage\"\n  (soup-aggregate\n    where: (owner: principal)\n    aggregate: (sum 'size)))"))
    (subsection
      "Bandwidth Limits"
      (code scheme "(define (enforce-bandwidth-limit principal bytes direction)\n  \"Enforce bandwidth quota\"\n  (let* ((quota (get-quota principal 'bandwidth))\n         (used (principal-bandwidth-used principal)))\n    (when (and quota (> (+ used bytes) quota))\n      (error 'bandwidth-quota-exceeded\n             `((quota . ,quota)\n               (used . ,used)\n               (requested . ,bytes)\n               (direction . ,direction))))))"))
    (subsection
      "Connection Limits"
      (code scheme "(define max-connections-per-principal 100)\n(define principal-connections (make-hash-table))\n\n(define (enforce-connection-limit principal)\n  \"Limit concurrent connections\"\n  (let ((count (hash-table-ref principal-connections principal 0)))\n    (when (>= count max-connections-per-principal)\n      (error 'connection-limit-exceeded\n             `((limit . ,max-connections-per-principal)\n               (current . ,count))))))\n\n(define (track-connection principal direction)\n  (let ((count (hash-table-ref principal-connections principal 0)))\n    (hash-table-set! principal-connections principal\n      (case direction\n        ((open) (+ count 1))\n        ((close) (max 0 (- count 1)))))))")))
  (section
    "Backpressure"
    (subsection
      "Request Queuing"
      (code scheme "(define request-queue (make-bounded-queue 1000))\n\n(define (queue-request request)\n  \"Queue request with backpressure\"\n  (if (queue-full? request-queue)\n      (begin\n        (audit-append action: 'request-rejected reason: 'queue-full)\n        (error 'service-unavailable))\n      (queue-push! request-queue request)))"))
    (subsection
      "Load Shedding"
      (code scheme "(define (should-shed-load?)\n  \"Determine if load shedding needed\"\n  (or (> (cpu-usage) 0.9)\n      (> (memory-usage) 0.9)\n      (> (queue-length request-queue) 800)))\n\n(define (shed-load request)\n  \"Selectively reject requests under load\"\n  (cond\n    ;; Always allow admin requests\n    ((admin-principal? (request-principal request))\n     (process-request request))\n    ;; Shed low-priority requests\n    ((and (should-shed-load?)\n          (low-priority-request? request))\n     (audit-append action: 'load-shed request: (request-id request))\n     (error 'service-unavailable))\n    (else\n     (process-request request))))"))
    (subsection
      "Retry-After"
      (code scheme "(define (rate-limit-response retry-after)\n  \"Generate rate limit response\"\n  `((status . 429)\n    (headers . ((Retry-After . ,retry-after)\n                (X-RateLimit-Limit . ,(current-limit))\n                (X-RateLimit-Remaining . ,(remaining-tokens))\n                (X-RateLimit-Reset . ,(reset-time))))))")))
  (section
    "Monitoring"
    (subsection
      "Limit Metrics"
      (code scheme "(define (record-limit-metrics)\n  \"Record rate limiting metrics\"\n  (metric-set! 'ratelimit.requests.allowed allowed-count)\n  (metric-set! 'ratelimit.requests.denied denied-count)\n  (metric-set! 'ratelimit.requests.queued (queue-length request-queue))\n  (metric-set! 'quota.storage.used total-storage-used)\n  (metric-set! 'quota.storage.available total-storage-available))"))
    (subsection
      "Limit Alerts"
      (code scheme "(define limit-alerts\n  '((high-rejection-rate\n     (condition (> (/ denied-count (+ allowed-count denied-count)) 0.1))\n     (severity warning)\n     (message \"High rate limit rejection rate\"))\n\n    (quota-near-limit\n     (condition (> (/ used quota) 0.9))\n     (severity warning)\n     (message \"Principal approaching quota limit\"))))")))
  (section
    "Configuration"
    (subsection
      "Dynamic Limits"
      (code scheme ";; Limits can be adjusted at runtime\n(define (set-limit principal limit-type value)\n  \"Set custom limit for principal\"\n  (soup-put\n    `((type . principal-limit)\n      (principal . ,principal)\n      (limit-type . ,limit-type)\n      (value . ,value)\n      (set-by . ,(current-principal))\n      (set-at . ,(current-time)))\n    type: 'configuration))\n\n(define (get-effective-limit principal limit-type)\n  \"Get principal's effective limit\"\n  (or (soup-query-one type: 'principal-limit\n                      principal: principal\n                      limit-type: limit-type)\n      (tier-limit (principal-tier principal) limit-type)))"))
    (subsection
      "Limit Inheritance"
      (code scheme ";; Groups can have limits that members inherit\n(define (group-limit group limit-type)\n  (soup-query-one type: 'group-limit\n                  group: group\n                  limit-type: limit-type))\n\n(define (effective-limit principal limit-type)\n  \"Resolve limit with inheritance\"\n  (or (get-effective-limit principal limit-type)\n      (let ((groups (principal-groups principal)))\n        (find (lambda (g) (group-limit g limit-type)) groups))\n      (default-limit limit-type)))")))
  (section
    "Security"
    (subsection
      "Limit Bypass Prevention"
      (code scheme ";; Prevent limit bypass via identity rotation\n(define (track-ip-limits ip)\n  \"Track limits by IP in addition to principal\"\n  (let ((limiter (get-ip-limiter ip)))\n    (unless (limiter 1)\n      (error 'ip-rate-limited))))\n\n;; Combine principal and IP limits\n(define (combined-rate-limit principal ip)\n  (and (rate-limit-principal principal)\n       (track-ip-limits ip)))"))
    (subsection
      "Audit Trail"
      (code scheme "(define (audit-limit-event event-type principal details)\n  (audit-append\n    action: event-type\n    principal: principal\n    details: details\n    timestamp: (current-time)))")))
  (section
    "References"
    (p "1. [Token Bucket Algorithm](https://en.wikipedia.org/wiki/Tokenbucket) 2. [Leaky Bucket Algorithm](https://en.wikipedia.org/wiki/Leakybucket) 3. [RFC-021: Capability Delegation](rfc-021-capability-delegation.html) 4. [RFC-031: Monitoring](rfc-031-monitoring.html)"))
  (section
    "Changelog"
    (list
      (item "2026-01-07")
      (item "Initial draft"))))

