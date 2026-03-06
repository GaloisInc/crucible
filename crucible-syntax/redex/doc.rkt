#lang racket/base

(require racket/cmdline
         racket/format
         racket/file
         redex/pict
         pict
         file/convertible
         "grammar.rkt"
         "typing.rkt")

;; --------------------------------------------------------------
;; Configuration

(define output-dir
  (command-line
   #:program "doc"
   #:args ([dir "doc"])
   dir))

;; --------------------------------------------------------------
;; Helpers

(define (save-svg! p filename)
  (define path (build-path output-dir filename))
  (define svg-bytes (convert p 'svg-bytes))
  (unless svg-bytes
    (error 'save-svg! "conversion to SVG failed for ~a" filename))
  (call-with-output-file path
    (lambda (out) (write-bytes svg-bytes out))
    #:exists 'replace)
  (printf "  ~a\n" path))

(define (heading txt)
  (text txt '(bold . modern) 14))

(define (section title . picts)
  (apply vc-append 10 (heading title) picts))

;; --------------------------------------------------------------
;; Render pieces

(printf "Rendering grammar...\n")
(define grammar-pict
  (section "Grammar" (render-language crucible-syntax)))

(printf "Rendering lookup judgments...\n")
(define lookup-pict
  (section "Lookup"
    (render-judgment-form lookup)
    (render-judgment-form fun-lookup)
    (render-judgment-form reg-lookup)
    (render-judgment-form global-lookup)))

(printf "Rendering expression typing...\n")
(define expr-pict
  (section "Expression Typing"
    (render-judgment-form expr-type)))

(printf "Rendering statement typing...\n")
(define stmt-pict
  (section "Statement Typing"
    (render-judgment-form stmt-ok)))

(printf "Rendering terminator typing...\n")
(define term-pict
  (section "Terminator Typing"
    (render-judgment-form term-ok)))

(printf "Rendering block & function typing...\n")
(define block-pict
  (section "Block Typing"
    (render-judgment-form stmts-ok)
    (render-judgment-form block-ok)
    (render-judgment-form blocks-ok)))

(define defun-pict
  (section "Function Typing"
    (render-judgment-form defun-ok)))

(define prog-pict
  (section "Program Typing"
    (render-judgment-form funs-ok)
    (render-judgment-form prog-ok)))

;; --------------------------------------------------------------
;; Write output

(make-directory* output-dir)

(printf "Writing SVG files to ~a/\n" output-dir)
(save-svg! grammar-pict "grammar.svg")
(save-svg! lookup-pict  "lookup.svg")
(save-svg! expr-pict    "expr-type.svg")
(save-svg! stmt-pict    "stmt-ok.svg")
(save-svg! term-pict    "term-ok.svg")
(save-svg! block-pict   "block-ok.svg")
(save-svg! defun-pict   "defun-ok.svg")
(save-svg! prog-pict    "prog-ok.svg")

;; Also write a combined single-page version
(define full-doc
  (vc-append 30
    grammar-pict
    lookup-pict
    expr-pict
    stmt-pict
    term-pict
    block-pict
    defun-pict
    prog-pict))
(save-svg! full-doc "spec.svg")

(printf "Done.\n")
