#lang racket/base

;; Fuzz-test the parser via Redex's random term generator.
;;
;; Property:  ∀ prog ∈ grammar.  parse(unparse(prog)) = prog
;;
;; We generate random programs from the Redex grammar, convert them
;; back to .cbl surface S-expressions, parse the surface forms, and
;; check that we recover the original AST.

(require redex/reduction-semantics
         racket/match
         racket/list
         racket/string
         racket/cmdline
         racket/port
         racket/pretty
         racket/system
         racket/file
         "grammar.rkt"
         "parse.rkt"
         "typing.rkt")

;; ================================================================
;; Unparser: internal Redex AST → .cbl surface S-expressions
;;
;; Reverses the transformations performed by parse.rkt so that
;; parse-forms(unparse(ast)) = ast.
;; ================================================================

;; Reverse strip-sigils: X86-80 → X86_80
(define (restore-sigils sexp)
  (cond
    [(and (symbol? sexp) (eq? sexp 'X86-80))
     (string->symbol "X86_80")]
    [(pair? sexp)
     (cons (restore-sigils (car sexp))
           (restore-sigils (cdr sexp)))]
    [else sexp]))

;; Reverse transform-expr
(define (unparse-expr e)
  (match e
    ;; () ← unit-val
    ['unit-val '()]
    ;; atoms pass through
    [#t #t] [#f #f]
    [(? number?) e]
    [(? string?) e]
    [(? symbol?) e]
    ;; $x ← (reg-ref $x)
    [`(reg-ref ,r)
     #:when (and (symbol? r)
                 (string-prefix? (symbol->string r) "$"))
     r]
    ;; $$x ← (global-ref $$x)
    [`(global-ref ,g)
     #:when (and (symbol? g)
                 (string-prefix? (symbol->string g) "$$"))
     g]
    ;; @f ← (fun-ref @f)
    [`(fun-ref ,f)
     #:when (and (symbol? f)
                 (string-prefix? (symbol->string f) "@"))
     f]
    ;; (the (Vector ty) (vector)) ← (the _ (empty-vector _))
    [`(the ,ty (empty-vector ,_))
     `(the ,ty (vector))]
    ;; (the (Maybe ty) nothing) ← (the _ (nothing _))
    [`(the ,ty (nothing ,_))
     `(the ,ty nothing)]
    ;; (the (Sequence ty) seq-nil) ← (the _ (seq-nil _))
    [`(the ,ty (seq-nil ,_))
     `(the ,ty seq-nil)]
    ;; (the ty (inj n e)) ← (the ty (inj ty n e))
    [`(the ,ty (inj ,_ ,n ,inner))
     `(the ,ty (inj ,n ,(unparse-expr inner)))]
    ;; (the ty e') ← (the ty e)
    [`(the ,ty ,inner)
     `(the ,ty ,(unparse-expr inner))]
    ;; schema-driven: recurse into sub-expression positions
    [`(,head ,args ...)
     (define schema (hash-ref expr-schemas head #f))
     (if schema
         (apply-schema head args schema unparse-expr)
         ;; no schema → pass through unchanged (parser also passes through)
         e)]
    [_ e]))

;; Reverse transform-stmt
(define (unparse-stmt s)
  (match s
    [`(breakpoint ,_ ,_) s]
    [`(,head ,args ...)
     (define schema (hash-ref stmt-schemas head #f))
     (if schema
         (apply-schema head args schema unparse-expr)
         s)]))

;; Reverse transform-term
(define (unparse-term t)
  (match t
    [`(,head ,args ...)
     (define schema (hash-ref term-schemas head #f))
     (if schema
         (apply-schema head args schema unparse-expr)
         t)]))

;; Reverse transform-block
(define (unparse-block blk)
  (match blk
    [`(defblock (,label ,x ,ty) ,body ...)
     (define stmts (drop-right body 1))
     (define term  (last body))
     `(defblock (,label ,x ,ty)
        ,@(map unparse-stmt stmts)
        ,(unparse-term term))]
    [`(,(and tag (or 'start 'defblock)) ,label ,body ...)
     (define stmts (drop-right body 1))
     (define term  (last body))
     `(,tag ,label
        ,@(map unparse-stmt stmts)
        ,(unparse-term term))]))

;; Reverse transform-defun
(define (unparse-defun d)
  (match d
    [`(defun ,name ,args ,ret-type (registers ,regs ...) ,blocks ...)
     `(defun ,name ,args ,ret-type
        (registers ,@regs) ,@(map unparse-block blocks))]
    [`(defun ,name ,args ,ret-type ,blocks ...)
     `(defun ,name ,args ,ret-type ,@(map unparse-block blocks))]))

(define (unparse-top-form f)
  (match f
    [`(defglobal ,_ ,_) f]
    [`(declare ,_ ,_ ,_) f]
    [`(extern ,_ ,_) f]
    [_ (unparse-defun f)]))

(define (unparse-prog prog)
  (map (lambda (f) (restore-sigils (unparse-top-form f))) prog))

;; ================================================================
;; Serialization: write surface S-expressions to .cbl format
;; ================================================================

(define (serialize-form form)
  (pretty-format form #:mode 'write))

(define (write-cbl-file path forms)
  (call-with-output-file path
    (lambda (out)
      (for ([f (in-list forms)])
        (write-string (serialize-form f) out)
        (newline out)))
    #:exists 'replace))

;; ================================================================
;; Type-checking
;; ================================================================

;; Check if a program is well-typed using the prog-ok judgment
(define (well-typed? ast)
  (judgment-holds (prog-ok ,ast)))

;; ================================================================
;; Test modes
;; ================================================================

;; Mode 1: Round-trip the Redex parser (always runs)
(define (fuzz-redex-round-trip attempts size)
  (printf "Fuzzing Redex parser round-trip (~a attempts, max size ~a)...\n"
          attempts size)
  (define passed 0)
  (redex-check crucible-syntax prog_0
    (let* ([ast     (term prog_0)]
           [surface (unparse-prog ast)]
           [reparsed (parse-forms surface)])
      (set! passed (add1 passed))
      (when (= 0 (modulo passed 100))
        (printf "  ...~a tests passed\n" passed))
      (equal? reparsed ast))
    #:attempts attempts
    #:attempt-size (lambda (n) (min n size)))
  (printf "  Redex round-trip: ok (~a tests)\n" passed))

;; Mode 2: Generate .cbl files for external testing
(define (generate-cbl-files dir count size)
  (make-directory* dir)
  (printf "Generating ~a .cbl files in ~a/ ...\n" count dir)
  (for ([i (in-range count)])
    (define ast (generate-term crucible-syntax prog_0 (min i size)))
    (define surface (unparse-prog ast))
    (define path (build-path dir (format "fuzz-~a.cbl" i)))
    (write-cbl-file path surface)
    (when (and (> i 0) (= 0 (modulo (add1 i) 100)))
      (printf "  ...~a files written\n" (add1 i))))
  (printf "  wrote ~a files\n" count))

;; Mode 3: Generate programs and check type statistics
(define (fuzz-crucible-check crucible-bin dir count size)
  (make-directory* dir)
  (printf "Generating and type-checking ~a programs...\n" count)

  (define well-typed-count 0)
  (define non-well-typed-count 0)
  (define parse-ok 0)
  (define parse-fail 0)

  ;; Generate and type-check all programs
  (define well-typed-files '())
  (for ([i (in-range count)])
    (define ast (generate-term crucible-syntax prog_0 (min i size)))
    (define surface (unparse-prog ast))
    (define path (build-path dir (format "fuzz-~a.cbl" i)))

    (if (well-typed? ast)
        (begin
          (set! well-typed-count (add1 well-typed-count))
          (write-cbl-file path surface)
          (set! well-typed-files (cons path well-typed-files)))
        (set! non-well-typed-count (add1 non-well-typed-count)))

    (when (and (> i 0) (= 0 (modulo (add1 i) 100)))
      (printf "  ...~a/~a programs processed (~a well-typed)\n"
              (add1 i) count well-typed-count)))

  (printf "\nType-checking results:\n")
  (printf "  Well-typed programs:     ~a (~a%)\n"
          well-typed-count
          (exact->inexact (* 100 (/ well-typed-count count))))
  (printf "  Non-well-typed programs: ~a (~a%)\n"
          non-well-typed-count
          (exact->inexact (* 100 (/ non-well-typed-count count))))

  ;; Test parser on well-typed programs if crucible-bin is provided
  (when crucible-bin
    (printf "\nTesting parser on well-typed programs...\n")
    (define check-path (build-path (current-directory) "check.rkt"))
    (define tested 0)
    (for ([path (in-list (reverse well-typed-files))])
      (define result
        (with-handlers ([exn:fail? (lambda (e)
                          (printf "  PARSE FAIL: ~a (exception: ~a)\n"
                                  path (exn-message e))
                          (set! parse-fail (add1 parse-fail))
                          #f)])
          (with-output-to-string
            (lambda ()
              (system (format "racket '~a' '~a' 2>&1"
                             (path->string check-path)
                             (path->string path)))))))
      (when result
        (if (string-contains? result "OK")
            (set! parse-ok (add1 parse-ok))
            (begin
              (printf "  PARSE FAIL: ~a\n  Output: ~a\n" path result)
              (set! parse-fail (add1 parse-fail)))))
      (set! tested (add1 tested))
      (when (and (> tested 0) (= 0 (modulo tested 100)))
        (printf "  ...~a/~a programs tested (~a ok, ~a failed)\n"
                tested (length well-typed-files) parse-ok parse-fail)))
    (printf "\nParser test results (well-typed programs only):\n")
    (printf "  Parse OK:   ~a\n" parse-ok)
    (printf "  Parse FAIL: ~a\n" parse-fail)
    (when (> parse-fail 0)
      (printf "\nWARNING: ~a well-typed programs failed to parse!\n" parse-fail))))

;; ================================================================
;; CLI
;; ================================================================

(module+ main
  (define attempts 1000)
  (define max-size 5)
  (define write-dir #f)
  (define crucible-bin #f)
  (define count 100)
  (define type-stats #f)

  (command-line
   #:program "fuzz"
   #:once-each
   [("-n" "--attempts") n "Number of redex-check attempts [1000]"
    (set! attempts (string->number n))]
   [("-s" "--size") s "Max term size [5]"
    (set! max-size (string->number s))]
   [("-w" "--write") dir "Write generated .cbl files to DIR"
    (set! write-dir dir)]
   [("-c" "--crucible") bin "Path to crucible binary (runs 'crucible check')"
    (set! crucible-bin bin)]
   [("--count") c "Number of .cbl files to generate [100]"
    (set! count (string->number c))]
   [("--type-stats") "Generate programs and report type-checking statistics"
    (set! type-stats #t)])

  (fuzz-redex-round-trip attempts max-size)

  (when write-dir
    (generate-cbl-files write-dir count max-size))

  (when (or crucible-bin type-stats)
    (fuzz-crucible-check (if crucible-bin crucible-bin #f)
      (or write-dir (make-temporary-file "fuzz-~a" 'directory))
      count max-size))

  (printf "Done.\n"))
