#!/usr/bin/env csi -s
;; The Cyberspace Librarian - Embedding Generator
;; Generate semantic embeddings for text using Ollama or OpenAI

(import scheme)
(import (chicken base))
(import (chicken port))
(import (chicken process-context))
(import (chicken process))
(import (chicken string))
(import (chicken io))
(import (chicken file))
(import (chicken time))
(import srfi-1)
(import srfi-13)

;; Will need these eggs for advanced features (install with: chicken-install <egg>)
;; (import http-client)  ; For native HTTP (currently using curl)
;; (import medea)        ; For robust JSON (currently using simple parser)
;; (import openssl)      ; For HTTPS support

;; ============================================================================
;; Configuration
;; ============================================================================

(define *ollama-endpoint* "http://localhost:11434/api/embeddings")
(define *ollama-model* "nomic-embed-text")

(define *openai-endpoint* "https://api.openai.com/v1/embeddings")
(define *openai-model* "text-embedding-3-small")

;; ============================================================================
;; Ollama Embeddings (Local, Recommended)
;; ============================================================================

(define (embed-with-ollama text)
  "Generate embedding using local Ollama instance"
  ;; Uses curl for HTTP POST (works without external eggs)
  (let ((temp-file (make-temp-filename)))
    (with-output-to-file temp-file
      (lambda ()
        (write-json `((model . ,*ollama-model*)
                      (prompt . ,text)))))

    (let* ((curl-cmd (string-append "curl -s -X POST " *ollama-endpoint*
                                    " -H 'Content-Type: application/json'"
                                    " -d @" temp-file))
           (result (with-input-from-pipe curl-cmd read-string)))
      (delete-file* temp-file)
      ;; Check if we got valid output
      (if (or (eof-object? result) (equal? result ""))
          (begin
            (print "ERROR: Failed to connect to Ollama at " *ollama-endpoint*)
            #f)
          (parse-ollama-response result)))))

(define (parse-ollama-response json-str)
  "Parse Ollama JSON response and extract embedding vector"
  ;; Ollama returns: {"embedding": [0.123, 0.456, ...]}
  ;; Simple parser for this specific format
  (let ((emb-start (string-contains json-str "\"embedding\":")))
    (if emb-start
        (let* ((array-start (string-index json-str #\[ emb-start))
               (array-end (string-index json-str #\] array-start))
               (array-str (substring json-str (+ array-start 1) array-end))
               (nums (string-split array-str ",")))
          (map (lambda (s) (string->number (string-trim-both s)))
               nums))
        (begin
          (print "Error parsing Ollama response: " (substring json-str 0 (min 200 (string-length json-str))))
          #f))))

;; ============================================================================
;; OpenAI Embeddings (API)
;; ============================================================================

(define (embed-with-openai text api-key)
  "Generate embedding using OpenAI API"
  ;; TODO: Implement HTTP POST with auth header
  (print "TODO: OpenAI embedding for text length: " (string-length text))
  #f)

;; ============================================================================
;; Generic Interface
;; ============================================================================

(define (embed-text text #!optional (backend 'ollama))
  "Generate embedding for text using specified backend"
  (case backend
    ((ollama) (embed-with-ollama text))
    ((openai) (embed-with-openai text (get-environment-variable "OPENAI_API_KEY")))
    (else (error "Unknown embedding backend:" backend))))

;; ============================================================================
;; Batch Processing
;; ============================================================================

(define (embed-documents docs #!optional (backend 'ollama))
  "Generate embeddings for list of documents"
  (map (lambda (doc)
         (let ((text (cdr (assoc 'content doc))))
           (cons (cons 'embedding (embed-text text backend))
                 doc)))
       docs))

;; ============================================================================
;; Similarity Calculation
;; ============================================================================

(define (cosine-similarity vec1 vec2)
  "Calculate cosine similarity between two vectors"
  ;; cos(θ) = (A·B) / (||A|| ||B||)
  (let ((dot-product (apply + (map * vec1 vec2)))
        (magnitude1 (sqrt (apply + (map (lambda (x) (* x x)) vec1))))
        (magnitude2 (sqrt (apply + (map (lambda (x) (* x x)) vec2)))))
    (/ dot-product (* magnitude1 magnitude2))))

(define (find-similar query-embedding doc-embeddings #!optional (top-k 10))
  "Find top-k most similar documents to query"
  (let ((scored (map (lambda (doc)
                       (let ((doc-emb (cdr (assoc 'embedding doc))))
                         (cons (cons 'similarity
                                     (cosine-similarity query-embedding doc-emb))
                               doc)))
                     doc-embeddings)))
    ;; Sort by similarity (descending) and take top-k
    (take (sort scored
                (lambda (a b)
                  (> (cdr (assoc 'similarity a))
                     (cdr (assoc 'similarity b)))))
          (min top-k (length scored)))))

;; ============================================================================
;; Helper Functions
;; ============================================================================

(define *temp-file-counter* 0)

(define (make-temp-filename)
  "Generate a temporary filename"
  (set! *temp-file-counter* (+ *temp-file-counter* 1))
  (string-append "/tmp/librarian-"
                 (number->string (current-seconds))
                 "-"
                 (number->string *temp-file-counter*)
                 ".json"))

(define (json-escape-string str)
  "Escape special characters in JSON string"
  ;; Basic escaping for quotes, newlines, backslashes
  (let loop ((chars (string->list str))
             (result '()))
    (if (null? chars)
        (list->string (reverse result))
        (let ((c (car chars)))
          (cond
           ((char=? c #\") (loop (cdr chars) (cons #\" (cons #\\ result))))
           ((char=? c #\\) (loop (cdr chars) (cons #\\ (cons #\\ result))))
           ((char=? c #\newline) (loop (cdr chars) (cons #\n (cons #\\ result))))
           ((char=? c #\return) (loop (cdr chars) (cons #\r (cons #\\ result))))
           ((char=? c #\tab) (loop (cdr chars) (cons #\t (cons #\\ result))))
           (else (loop (cdr chars) (cons c result))))))))

(define (write-json obj)
  "Write Scheme data structure as JSON"
  ;; Simplified JSON writer
  (cond
   ((list? obj)
    (display "{")
    (let loop ((lst obj) (first? #t))
      (unless (null? lst)
        (unless first? (display ","))
        (let ((pair (car lst)))
          (display "\"") (display (car pair)) (display "\":")
          (write-json (cdr pair)))
        (loop (cdr lst) #f)))
    (display "}"))
   ((string? obj)
    (display "\"") (display (json-escape-string obj)) (display "\""))
   (else
    (display obj))))

;; ============================================================================
;; Testing and CLI
;; ============================================================================

(define (test-embedding)
  "Test embedding generation with a simple query"
  (print "Testing Ollama embedding...")
  (print "Query: 'Papers about hash-based crypto before PKI'")
  (let ((embedding (embed-text "Papers about hash-based crypto before PKI")))
    (if embedding
        (begin
          (print "Success! Embedding vector length: " (length embedding))
          (print "First 10 dimensions: " (take* embedding 10))
          embedding)
        (begin
          (print "Failed to generate embedding. Is Ollama running?")
          (print "Start with: ollama pull nomic-embed-text && ollama serve")
          #f))))

(define (take* lst n)
  "Take up to n elements from list"
  (if (or (null? lst) (<= n 0))
      '()
      (cons (car lst) (take* (cdr lst) (- n 1)))))

(when (equal? (program-name) "csi")
  (print "Cyberspace Librarian - Embedding Generator")
  (print "")
  (print "Usage:")
  (print "  (embed-text \"your text here\")           ; Use Ollama (local)")
  (print "  (test-embedding)                         ; Test with sample query")
  (print "  (embed-text \"text\" 'openai)            ; Use OpenAI API")
  (print "")
  (print "Note: Requires Ollama running locally with nomic-embed-text model")
  (print "  Setup: ollama pull nomic-embed-text")
  (print ""))
