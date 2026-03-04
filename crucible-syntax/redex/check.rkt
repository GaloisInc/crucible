#lang racket/base

(require racket/cmdline
         redex/reduction-semantics
         "parse.rkt"
         "typing.rkt")

(define files
  (command-line
   #:program "check"
   #:args files files))

(define all-ok? #t)

(for ([f (in-list files)])
  (printf "~a ... " f)
  (with-handlers ([exn:fail? (lambda (e)
                    (printf "FAIL: ~a\n" (exn-message e))
                    (set! all-ok? #f))])
    (define forms (parse-file f))
    (if (or (null? forms) (judgment-holds (prog-ok ,forms)))
        (printf "OK\n")
        (begin (printf "FAIL\n") (set! all-ok? #f)))))

(exit (if all-ok? 0 1))
