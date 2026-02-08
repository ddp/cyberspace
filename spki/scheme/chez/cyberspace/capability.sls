;;; SPKI Scheme - Capability Scoring and Dynamic Scaling
;;; Library of Cyberspace - Chez Port
;;;
;;; Provides hardware capability scoring for automated master election
;;; and dynamic scaling factor computation from confederation members.
;;;
;;; Philosophy: "Most capable wins the realm" - the node with highest
;;; capability score becomes realm master during automated enrollment.
;;;
;;; Design principles:
;;;   - Prefer !mobile (servers/desktops over laptops)
;;;   - Normalize to capable (scaling relative to most capable member)

(library (cyberspace capability)
  (export
    ;; Capability scoring
    compute-capability-score
    capability-weights
    set-capability-weights!
    is-mobile?
    ;; Scaling factor (normalized to capable)
    compute-scaling-factor
    aggregate-confederation-resources
    ;; Auto-election
    elect-master
    compare-capabilities)

  (import (except (rnrs) find)
          (only (chezscheme) printf format void sort)
          (cyberspace chicken-compatibility chicken))

  ;; ============================================================
  ;; Capability Weights - Tunable parameters
  ;; ============================================================

  ;; Default weights prioritize weave > memory > storage
  ;; Weave (hashes/sec) measures actual compute, not just core count
  ;; Mobile penalty is severe - prefer !mobile
  (define *capability-weights*
    '((weave . 0.001)          ; ~1 point per 1000 hashes/sec
      (memory-gb . 2.0)
      (storage-gb . 0.5)
      (mobile-penalty . 0.1)))  ; mobile devices score 10% of desktop/server

  ;; ============================================================
  ;; Mobile Detection - Prefer !mobile
  ;; ============================================================

  (define *mobile-models*
    ;; Model substrings that indicate mobile devices
    '("MacBook" "Macbook" "Book" "Laptop" "laptop"
      "iPad" "iPhone" "Surface" "ThinkPad" "XPS"))

  (define (is-mobile? hw)
    "Detect if hardware is a mobile device.
     Returns #t for laptops/tablets, #f for desktops/servers."
    (let ((model (extract-hardware-value-str hw 'model)))
      (if model
          (any (lambda (pattern)
                 (str-contains-ci model pattern))
               *mobile-models*)
          #f)))  ; unknown = assume !mobile

  (define (extract-hardware-value-str hw key)
    "Extract string value from hardware introspection"
    (let ((pair (assq key (cdr hw))))
      (if pair
          (let ((val (cadr pair)))
            (if (string? val) val #f))
          #f)))

  (define (str-contains-ci str pattern)
    "Case-insensitive substring search"
    (let ((str-down (str-downcase str))
          (pat-down (str-downcase pattern)))
      (str-contains str-down pat-down)))

  (define (str-contains str pattern)
    "Check if str contains pattern"
    (let ((slen (string-length str))
          (plen (string-length pattern)))
      (let loop ((i 0))
        (cond ((> (+ i plen) slen) #f)
              ((string=? (substring str i (+ i plen)) pattern) #t)
              (else (loop (+ i 1)))))))

  (define (str-downcase str)
    "Convert string to lowercase"
    (list->string
     (map char-downcase (string->list str))))

  (define (capability-weights)
    "Get current capability weights"
    *capability-weights*)

  (define (set-capability-weights! weights)
    "Set capability weights alist"
    (set! *capability-weights* weights))

  ;; ============================================================
  ;; Capability Scoring
  ;; ============================================================

  (define (get-weight key)
    "Get weight for a capability dimension"
    (let ((pair (assq key *capability-weights*)))
      (if pair (cdr pair) 0.0)))

  (define (extract-hardware-value hw key)
    "Extract numeric value from hardware introspection"
    (let ((pair (assq key (cdr hw))))
      (if pair
          (let ((val (cadr pair)))
            (if (number? val) val 0))
          0)))

  (define (compute-capability-score hw)
    "Compute capability score from hardware introspection.

     hw: result of (introspect-hardware) - must include (mobile #t/#f)
     Returns: numeric score (higher = more capable)

     Scoring formula:
       base = (weave * w_weave) + (memory * w_memory) + (storage * w_storage)
       score = base * (mobile-penalty if mobile, else 1.0)"

    (let* ((weave (extract-hardware-value hw 'weave))
           (memory (extract-hardware-value hw 'memory-gb))
           (storage (or (extract-hardware-value hw 'root-avail-gb) 0))
           (base-score (+ (* weave (get-weight 'weave))
                          (* memory (get-weight 'memory-gb))
                          (* storage (get-weight 'storage-gb))))
           ;; Check mobile flag from hw, or detect from model
           (mobile (let ((flag (assq 'mobile (cdr hw))))
                    (if flag (cadr flag) (is-mobile? hw))))
           (multiplier (if mobile (get-weight 'mobile-penalty) 1.0)))
      (* base-score multiplier)))

  (define (compare-capabilities hw1 hw2)
    "Compare two hardware specs.
     Returns: 'first if hw1 > hw2, 'second if hw2 > hw1, 'tie if equal"
    (let ((score1 (compute-capability-score hw1))
          (score2 (compute-capability-score hw2)))
      (cond ((> score1 score2) 'first)
            ((> score2 score1) 'second)
            (else 'tie))))

  ;; ============================================================
  ;; Master Election - Most Capable Wins the Realm
  ;; ============================================================

  (define (elect-master candidates)
    "Elect master from list of candidates.
     candidates: list of (name . hardware) pairs
     Returns: (values winner-name winner-score all-scores)"

    (if (null? candidates)
        (values #f 0 '())
        (let* ((scored (map (lambda (c)
                              (cons (car c)
                                    (compute-capability-score (cdr c))))
                            candidates))
               (sorted (sort (lambda (a b) (> (cdr a) (cdr b))) scored))
               (winner (car sorted)))
          (values (car winner) (cdr winner) scored))))

  ;; ============================================================
  ;; Dynamic Scaling Factor
  ;; ============================================================

  (define (aggregate-confederation-resources members)
    "Aggregate resources from all confederation members.
     members: list of hardware introspection results
     Returns: alist of aggregated resources"

    (let loop ((members members)
               (cores 0)
               (memory 0)
               (storage 0)
               (count 0))
      (if (null? members)
          `((total-cores . ,cores)
            (total-memory-gb . ,memory)
            (total-storage-gb . ,storage)
            (member-count . ,count))
          (let ((hw (car members)))
            (loop (cdr members)
                  (+ cores (extract-hardware-value hw 'cores))
                  (+ memory (extract-hardware-value hw 'memory-gb))
                  (+ storage (or (extract-hardware-value hw 'root-avail-gb) 0))
                  (+ count 1))))))

  (define (compute-scaling-factor members)
    "Compute dynamic scaling factor normalized to the most capable member.
     members: list of (name . hardware) pairs
     Returns: alist with per-member scaling factors and aggregate stats"

    (if (null? members)
        '((reference . #f)
          (reference-score . 0)
          (members . ())
          (aggregate-score . 0)
          (member-count . 0)
          (effective-capacity . 0)
          (recommended-replication . 0))

        (let* (;; Score all members
               (scored (map (lambda (m)
                              (cons (car m)
                                    (compute-capability-score (cdr m))))
                            members))

               ;; Find the most capable (reference)
               (sorted (sort (lambda (a b) (> (cdr a) (cdr b))) scored))
               (reference (car sorted))
               (ref-name (car reference))
               (ref-score (cdr reference))

               ;; Normalize all to reference
               (normalized (map (lambda (s)
                                  (cons (car s)
                                        (if (> ref-score 0)
                                            (/ (cdr s) ref-score)
                                            0)))
                                scored))

               ;; Aggregate stats
               (aggregate (apply + (map cdr scored)))
               (count (length members))
               (effective (if (> ref-score 0)
                             (/ aggregate ref-score)
                             0)))

          `((reference . ,ref-name)
            (reference-score . ,(inexact ref-score))
            (members . ,(map (lambda (n)
                               (cons (car n) (inexact (cdr n))))
                             normalized))
            (aggregate-score . ,(inexact aggregate))
            (member-count . ,count)
            (effective-capacity . ,(inexact effective))
            (recommended-replication . ,(min count 3))))))

) ;; end library
