;;;; directory-repl.scm --- Interactive Directory REPL
;;;; "Peace for All Mankind" - Finding knowledge should be delightful
;;;;
;;;; An intelligent, helpful REPL for exploring the cyberspace library.
;;;; Understands natural language queries and guides you to what you need.

(import scheme
        (chicken base)
        (chicken format)
        (chicken io)
        (chicken string)
        srfi-1
        srfi-13
        srfi-69)

(import directory)

;;;; ========================================================================
;;;; Smart Query Parser
;;;; ========================================================================

;;; Parse natural language queries into structured searches
(define (parse-query query-string library)
  (let ((query (string-downcase query-string)))
    (cond
     ;; Author queries
     ((or (string-contains query "by ")
          (string-contains query "author:"))
      (parse-author-query query library))

     ;; Year queries
     ((or (string-contains query "from ")
          (string-contains query "in ")
          (string-match "[0-9]{4}" query))
      (parse-year-query query library))

     ;; Topic queries
     ((or (string-contains query "about ")
          (string-contains query "topic:"))
      (parse-topic-query query library))

     ;; Collection queries
     ((or (string-contains query "collection:")
          (string-contains query "in collection"))
      (parse-collection-query query library))

     ;; General keyword search
     (else
      (search-documents library query)))))

;;; Parse author query ("papers by Lampson", "author:Rivest")
(define (parse-author-query query library)
  (let* ((author-name
          (cond
           ((string-contains query "by ")
            (substring/shared query (+ 3 (string-contains query "by "))))
           ((string-contains query "author:")
            (substring/shared query (+ 7 (string-contains query "author:"))))
           (else query)))
         (cleaned-name (string-trim-both author-name)))
    (find-by-author-fuzzy library cleaned-name)))

;;; Fuzzy author search (handles partial names)
(define (find-by-author-fuzzy library partial-name)
  (let ((all-authors (hash-table-keys (library-author-index library))))
    (let ((matches (filter (lambda (author)
                            (string-contains-ci author partial-name))
                          all-authors)))
      (if (null? matches)
          '()
          (apply append (map (lambda (author)
                              (find-by-author library author))
                            matches))))))

;;; Parse year query ("papers from 1971", "in 1999")
(define (parse-year-query query library)
  (let ((year-match (string-search "[0-9]{4}" query)))
    (if year-match
        (let ((year (string->number (substring query
                                              (car year-match)
                                              (cdr year-match)))))
          (find-by-year library year))
        '())))

;;; Parse topic query ("about authentication", "topic:SPKI")
(define (parse-topic-query query library)
  (let* ((topic
          (cond
           ((string-contains query "about ")
            (substring/shared query (+ 6 (string-contains query "about "))))
           ((string-contains query "topic:")
            (substring/shared query (+ 6 (string-contains query "topic:"))))
           (else query)))
         (cleaned-topic (string-trim-both topic)))
    (find-by-topic-fuzzy library cleaned-topic)))

;;; Fuzzy topic search
(define (find-by-topic-fuzzy library partial-topic)
  (let ((all-topics (hash-table-keys (library-topic-index library))))
    (let ((matches (filter (lambda (topic)
                            (string-contains-ci topic partial-topic))
                          all-topics)))
      (if (null? matches)
          '()
          (apply append (map (lambda (topic)
                              (find-by-topic library topic))
                            matches))))))

;;; Parse collection query
(define (parse-collection-query query library)
  (let* ((coll-name
          (cond
           ((string-contains query "collection:")
            (substring/shared query (+ 11 (string-contains query "collection:"))))
           ((string-contains query "in collection ")
            (substring/shared query (+ 14 (string-contains query "in collection "))))
           (else query)))
         (cleaned-name (string-trim-both coll-name)))
    (find-in-collection library cleaned-name)))

;;;; ========================================================================
;;;; Beautiful Display
;;;; ========================================================================

;;; Display search results beautifully
(define (display-results results query)
  (cond
   ((null? results)
    (printf "~%🔍 No results found for: ~A~%" query)
    (printf "   Try: 'help' for search tips~%"))

   ((= 1 (length results))
    (printf "~%📄 Found 1 document:~%~%")
    (display-document-brief (car results) 1))

   (else
    (printf "~%📚 Found ~A documents:~%~%" (length results))
    (for-each (lambda (doc idx)
                (display-document-brief doc idx))
              results
              (iota (length results) 1)))))

;;; Display a document in brief format (for lists)
(define (display-document-brief doc index)
  (printf " [~A] ~A~%" index (document-title doc))
  (printf "     👤 ~A~%" (string-join (document-authors doc) ", "))
  (printf "     📅 ~A  📁 ~A~%~%"
          (or (document-year doc) "n/a")
          (document-collection doc)))

;;; Display document in full detail
(define (display-document-full doc)
  (printf "~%╔═══════════════════════════════════════════════════════════════╗~%")
  (printf "║ ~A~%" (pad-string (document-title doc) 61))
  (printf "╚═══════════════════════════════════════════════════════════════╝~%~%")
  (printf "👤  Authors:    ~A~%" (string-join (document-authors doc) ", "))
  (printf "📅  Year:       ~A~%" (or (document-year doc) "Unknown"))
  (printf "📁  Collection: ~A~%" (document-collection doc))
  (printf "📂  File:       ~A~%" (document-file-path doc))
  (when (not (null? (document-topics doc)))
    (printf "🏷️   Topics:     ~A~%" (string-join (document-topics doc) ", ")))
  (when (document-citations doc)
    (printf "~%📖  Citation:~%    ~A~%" (document-citations doc)))
  (printf "~%"))

;;; Pad string to width (helper)
(define (pad-string str width)
  (if (> (string-length str) width)
      (substring str 0 (- width 3))
      (string-append str (make-string (- width (string-length str)) #\space))))

;;;; ========================================================================
;;;; Interactive REPL
;;;; ========================================================================

;;; Print welcome banner
(define (print-banner)
  (printf "~%")
  (printf "╔═════════════════════════════════════════════════════════════════╗~%")
  (printf "║  📚 Cyberspace Library Directory                               ║~%")
  (printf "║  \"Peace for All Mankind\" - Finding knowledge should be joyful  ║~%")
  (printf "╚═════════════════════════════════════════════════════════════════╝~%")
  (printf "~%"))

;;; Print help message
(define (print-help)
  (printf "~%🎯 Natural Language Search:~%")
  (printf "   • 'papers by Lampson'       - Find by author~%")
  (printf "   • 'about authentication'     - Find by topic~%")
  (printf "   • 'from 1971'                - Find by year~%")
  (printf "   • 'in collection lampson'    - Browse collection~%")
  (printf "   • 'SPKI'                     - Keyword search~%")
  (printf "~%⚡ Commands:~%")
  (printf "   • stats                      - Library statistics~%")
  (printf "   • collections                - List all collections~%")
  (printf "   • authors                    - List all authors~%")
  (printf "   • topics                     - List all topics~%")
  (printf "   • years                      - List all years~%")
  (printf "   • help                       - Show this help~%")
  (printf "   • quit                       - Exit REPL~%")
  (printf "~%💡 Tips:~%")
  (printf "   • Partial names work: 'Lamp' finds Lampson, Lamport~%")
  (printf "   • Case insensitive: 'SPKI' = 'spki'~%")
  (printf "   • Combine terms: 'Rivest SDSI'~%")
  (printf "~%"))

;;; Main REPL loop
(define (directory-repl library)
  (print-banner)
  (printf "Loaded ~A documents from ~A collections~%"
          (length (library-documents library))
          (length (library-collections library)))
  (printf "Type 'help' for search tips, 'quit' to exit~%~%")

  (let loop ()
    (printf "📖 > ")
    (flush-output)
    (let ((input (read-line)))
      (cond
       ((eof-object? input)
        (printf "~%👋 Goodbye!~%"))

       ((string=? (string-trim-both input) "quit")
        (printf "~%👋 Goodbye!~%"))

       ((string=? (string-trim-both input) "help")
        (print-help)
        (loop))

       ((string=? (string-trim-both input) "stats")
        (display-library-stats library)
        (loop))

       ((string=? (string-trim-both input) "collections")
        (display-collections library)
        (loop))

       ((string=? (string-trim-both input) "authors")
        (display-authors library)
        (loop))

       ((string=? (string-trim-both input) "topics")
        (display-topics library)
        (loop))

       ((string=? (string-trim-both input) "years")
        (display-years library)
        (loop))

       ((string=? (string-trim-both input) "")
        (loop))

       (else
        (let ((results (parse-query input library)))
          (display-results results input)
          (loop)))))))

;;; Display all collections
(define (display-collections library)
  (printf "~%📚 Collections:~%~%")
  (for-each (lambda (coll idx)
              (printf " [~A] ~A (~A docs)~%"
                      idx
                      (collection-name coll)
                      (length (collection-documents coll))))
            (library-collections library)
            (iota (length (library-collections library)) 1)))

;;; Display all authors (top 20)
(define (display-authors library)
  (let ((authors (sort (hash-table-keys (library-author-index library))
                      string<?)))
    (printf "~%👥 Authors (~A total, showing first 20):~%~%" (length authors))
    (for-each (lambda (author)
                (printf "   • ~A (~A papers)~%"
                        author
                        (length (find-by-author library author))))
              (take authors (min 20 (length authors))))))

;;; Display all topics (top 20)
(define (display-topics library)
  (let ((topics (generate-topic-index library)))
    (printf "~%🏷️  Topics (~A total, showing top 20 by frequency):~%~%"
            (length topics))
    (for-each (lambda (topic)
                (printf "   • ~A (~A papers)~%"
                        topic
                        (length (find-by-topic library topic))))
              (take topics (min 20 (length topics))))))

;;; Display all years
(define (display-years library)
  (let ((years (generate-chronological-index library)))
    (printf "~%📅 Years (~A - ~A):~%~%"
            (car years)
            (last years))
    (for-each (lambda (year)
                (printf "   • ~A: ~A papers~%"
                        year
                        (length (find-by-year library year))))
              years)))

;;;; ========================================================================
;;;; Entry Point
;;;; ========================================================================

;;; Main entry point
(define (main)
  (let ((library-path (or (get-environment-variable "CYBERSPACE_HOME")
                          (get-environment-variable "HOME"))))
    (printf "Loading cyberspace library from ~A...~%" library-path)
    (let ((lib (load-library library-path)))
      (directory-repl lib))))

;; Run if executed as script
(when (eq? (car (argv)) "directory-repl.scm")
  (main))
