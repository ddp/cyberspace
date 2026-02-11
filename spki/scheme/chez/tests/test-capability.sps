;;; Capability Scoring Tests - Chez Scheme Port
;;; Tests capability scoring, mobile penalty, scaling, master election.

(import (rnrs)
        (only (chezscheme) printf format)
        (cyberspace chicken-compatibility chicken)
        (cyberspace test)
        (cyberspace capability)
        (cyberspace crypto-ffi))

;; Initialize libsodium
(sodium-init)

;; Test Fixtures
(define hw-server
  '(hardware
    (model "Mac Studio M3 Max")
    (mobile #f)
    (weave 2000000)
    (memory-gb 128)
    (root-avail-gb 1000)))

(define hw-laptop
  '(hardware
    (model "MacBook Air M2")
    (mobile #t)
    (weave 500000)
    (memory-gb 16)
    (root-avail-gb 256)))

(define hw-mini
  '(hardware
    (model "Mac mini M4")
    (mobile #f)
    (weave 1500000)
    (memory-gb 32)
    (root-avail-gb 512)))

(printf "~n=== Capability Scoring Tests ===~n~n")

(test "server scores higher than mobile"
  (lambda ()
    (let ((server-score (compute-capability-score hw-server))
          (laptop-score (compute-capability-score hw-laptop)))
      (> server-score laptop-score))))

(test "mobile penalty is approximately 10x"
  (lambda ()
    (let* ((hw-base '(hardware
                      (model "Test")
                      (mobile #f)
                      (weave 1000000)
                      (memory-gb 64)
                      (root-avail-gb 500)))
           (hw-mobile '(hardware
                        (model "Test")
                        (mobile #t)
                        (weave 1000000)
                        (memory-gb 64)
                        (root-avail-gb 500)))
           (base-score (compute-capability-score hw-base))
           (mobile-score (compute-capability-score hw-mobile))
           (ratio (/ base-score mobile-score)))
      (and (> ratio 8.0) (< ratio 12.0)))))

(test "is-mobile? detects mobile devices"
  (lambda ()
    (and (is-mobile? hw-laptop)
         (not (is-mobile? hw-server))
         (not (is-mobile? hw-mini)))))

(test "elect-master picks most capable"
  (lambda ()
    (let ((candidates (list (cons 'server hw-server)
                            (cons 'laptop hw-laptop)
                            (cons 'mini hw-mini))))
      (let-values (((winner score all-scores) (elect-master candidates)))
        (eq? winner 'server)))))

(test "elect-master prefers non-mobile at similar capability"
  (lambda ()
    (let ((candidates (list (cons 'mini hw-mini)
                            (cons 'laptop hw-laptop))))
      (let-values (((winner score all-scores) (elect-master candidates)))
        (eq? winner 'mini)))))

(test "elect-master handles single candidate"
  (lambda ()
    (let ((candidates (list (cons 'solo hw-laptop))))
      (let-values (((winner score all-scores) (elect-master candidates)))
        (eq? winner 'solo)))))

(test "compare-capabilities returns correct ordering"
  (lambda ()
    (and (eq? 'first (compare-capabilities hw-server hw-laptop))
         (eq? 'second (compare-capabilities hw-laptop hw-server)))))

(test "compute-scaling-factor normalization to reference"
  (lambda ()
    (let* ((members (list (cons 'server hw-server)
                          (cons 'mini hw-mini)
                          (cons 'laptop hw-laptop)))
           (scaling (compute-scaling-factor members))
           (member-scales (alist-ref 'members scaling))
           (ref (alist-ref 'reference scaling)))
      (and (eq? ref 'server)
           (= 1.0 (alist-ref 'server member-scales))
           (< (alist-ref 'mini member-scales) 1.0)
           (< (alist-ref 'laptop member-scales) 1.0)))))

(test "effective-capacity grows with members"
  (lambda ()
    (let* ((single (compute-scaling-factor
                     (list (cons 'server hw-server))))
           (multi (compute-scaling-factor
                    (list (cons 'server hw-server)
                          (cons 'mini hw-mini)))))
      (> (alist-ref 'effective-capacity multi)
         (alist-ref 'effective-capacity single)))))

(test "capability score is positive"
  (lambda ()
    (and (> (compute-capability-score hw-server) 0)
         (> (compute-capability-score hw-laptop) 0)
         (> (compute-capability-score hw-mini) 0))))

(test-summary)
