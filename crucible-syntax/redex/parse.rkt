#lang racket/base

(require racket/match
         racket/list
         racket/string
         racket/port)

(provide parse-file parse-forms
         expr-schemas stmt-schemas term-schemas apply-schema)

;; Desugar .cbl surface syntax into explicit Redex grammar forms:
;;   ()→unit-val, $x→(reg-ref $x), $$x→(global-ref $$x), @f→(fun-ref @f),
;;   hex literals→numbers, type propagation into inj/nothing/empty-vector/seq-nil.

;; --------------------------------------------------------------
;; Argument schemas for expression, statement, and terminator forms.
;;
;; Each entry maps a head symbol to a list of argument descriptors:
;;   e  — sub-expression: apply transform-expr recursively
;;   _  — raw value: pass through unchanged (types, numbers, labels)
;;   e* — variadic trailing expressions (must be last in schema)
;;   _* — variadic trailing raw values (must be last in schema)

(define expr-schemas
  (for/hasheq ([entry '(
    (the _ e)
    (+ e e e*) (- e e e*) (* e e e*) (/ e e) (mod e e)
    (< e e) (<= e e) (equal? e e)
    (negate e) (abs e)
    (and e e e*) (or e e e*) (xor e e e*) (not e)
    (integer? e)
    (if e e e)
    (string-concat e e) (show e) (fresh _)
    (string-empty _) (string-length e)
    (to-any e) (from-any _ e)
    (just e) (from-just e e)
    (bv _ _)
    (bv-xor e e e*) (bv-or e e e*)
    (bv-and e e) (bv-not e)
    (shl e e) (lshr e e) (ashr e e)
    (bool-to-bv _ e) (zero-extend _ e) (sign-extend _ e)
    (bv-concat e e) (bv-trunc _ e) (bv-select _ _ e)
    (bv-nonzero e)
    (bv-carry e e) (bv-scarry e e) (bv-sborrow e e)
    (<$ e e) (<=$ e e) (/$ e e) (smod e e)
    (binary-to-fp _ e) (fp-to-binary e)
    (ubv-to-fp _ _ e) (sbv-to-fp _ _ e)
    (fp-to-ubv _ _ e) (fp-to-sbv _ _ e)
    (fp-to-real e) (real-to-fp _ _ e)
    (ref e) (deref e)
    (get-field _ e) (set-field e _ e)
    (struct e*) (vector e*)
    (proj _ e)
    (seq-cons e e) (seq-append e e)
    (seq-nil? e) (seq-length e)
    (seq-head e) (seq-tail e) (seq-uncons e)
    (vector-replicate e e) (vector-empty? e)
    (vector-size e) (vector-get e e)
    (vector-set e e e) (vector-cons e e)
    (funcall _ e*) (fun-ref _)
    )])
    (values (car entry) (cdr entry))))

(define stmt-schemas
  (for/hasheq ([entry '(
    (let _ e)
    (print e)
    (println e)
    (funcall _ e*)
    (set-register! _ e)
    (set-global! _ e)
    (assert! e e)
    (assume! e e)
    (set-ref! e e)
    (drop-ref! e)
    )])
    (values (car entry) (cdr entry))))

(define term-schemas
  (for/hasheq ([entry '(
    (return e)
    (jump _)
    (branch e _ _)
    (error e)
    (output _ e)
    (maybe-branch e _ _)
    (case e _*)
    (tail-call _ e*)
    )])
    (values (car entry) (cdr entry))))

;; --------------------------------------------------------------
;; Generic schema-driven transformer

(define (apply-schema head args schema transform)
  (define has-var?
    (and (pair? schema) (memq (last schema) '(e* _*))))
  (define var-kind (and has-var? (last schema)))
  (define fixed (if has-var? (drop-right schema 1) schema))
  (define n (length fixed))
  (define (process-raw-value v)
    (if (symbol? v)
        (or (try-hex-convert v) v)
        v))
  `(,head
    ,@(for/list ([a (in-list (take args n))]
                 [s (in-list fixed)])
        (if (eq? s 'e) (transform a) (process-raw-value a)))
    ,@(cond
        [(eq? var-kind 'e*) (map transform (drop args n))]
        [(eq? var-kind '_*) (map process-raw-value (drop args n))]
        [else (drop args n)])))

;; --------------------------------------------------------------
;; Hex literal conversion
(define (try-hex-convert sym)
  (define s (symbol->string sym))
  (cond
    [(regexp-match #rx"^0x([0-9a-fA-F]+)/([0-9]+)$" s)
     => (lambda (m) (/ (string->number (cadr m) 16)
                  (string->number (caddr m))))]
    [(regexp-match #rx"^0x([0-9a-fA-F]+)$" s)
     => (lambda (m) (string->number (cadr m) 16))]
    [else #f]))

;; --------------------------------------------------------------
;; Pass 1: cosmetic normalization
;;   - rename X86_80 → X86-80 (Redex disallows _ in symbols)
;;   (block labels keep their : suffix to avoid colliding with grammar keywords)
(define (strip-sigils sexp)
  (cond
    [(symbol? sexp)
     (let ([s (symbol->string sexp)])
       (cond
         [(equal? s "X86_80") (string->symbol "X86-80")]
         [else sexp]))]
    [(pair? sexp)
     (cons (strip-sigils (car sexp))
           (strip-sigils (cdr sexp)))]
    [else sexp]))

;; --------------------------------------------------------------
;; Pass 2: transform expressions, statements, terminators

(define (transform-expr e)
  (cond
    [(null? e) 'unit-val]
    [(symbol? e)
     (define s (symbol->string e))
     (define hex (try-hex-convert e))
     (cond
       [hex hex]
       [(string-prefix? s "$$") `(global-ref ,e)]
       [(string-prefix? s "$")  `(reg-ref ,e)]
       [(string-prefix? s "@")  `(fun-ref ,e)]
       [else e])]
    [(pair? e)
     (define head (car e))
     (define args (cdr e))
     (match e
       ;; Special: push variant type into inj
       [`(the ,ty (inj ,n ,inner))
        `(the ,ty (inj ,ty ,n ,(transform-expr inner)))]
       ;; Special: (vector) with no args → (empty-vector ty)
       [`(the (Vector ,ety) (vector))
        `(the (Vector ,ety) (empty-vector ,ety))]
       ;; Schema-driven generic case
       [_ (define schema (hash-ref expr-schemas head #f))
          (if schema
              (apply-schema head args schema transform-expr)
              e)])]
    [else e]))

(define (transform-stmt s)
  (match s
    [`(breakpoint ,label ,vars) s]
    [`(,head ,args ...)
     (define schema (hash-ref stmt-schemas head #f))
     (if schema
         (apply-schema head args schema transform-expr)
         (error 'transform-stmt "unknown form: ~a" head))]))

(define (transform-term t)
  (match t
    [`(,head ,args ...)
     (define schema (hash-ref term-schemas head #f))
     (if schema
         (apply-schema head args schema transform-expr)
         (error 'transform-term "unknown form: ~a" head))]))

;; --------------------------------------------------------------
;; Block and function transforms

(define (transform-block blk)
  (match blk
    [`(defblock (,label ,x ,ty) ,body ...)
     (define stmts (drop-right body 1))
     (define term (last body))
     `(defblock (,label ,x ,ty)
        ,@(map transform-stmt stmts)
        ,(transform-term term))]
    [`(,(and tag (or 'start 'defblock)) ,label ,body ...)
     (define stmts (drop-right body 1))
     (define term (last body))
     `(,tag ,label
        ,@(map transform-stmt stmts)
        ,(transform-term term))]))

(define (transform-defun d)
  (match d
    [`(defun ,name ,args ,ret-type (registers ,regs ...) ,blocks ...)
     `(defun ,name ,args ,ret-type
        (registers ,@regs) ,@(map transform-block blocks))]
    [`(defun ,name ,args ,ret-type ,blocks ...)
     `(defun ,name ,args ,ret-type ,@(map transform-block blocks))]))

;; --------------------------------------------------------------
;; Main entry point

(define (parse-forms forms)
  (map (lambda (f)
         (define stripped (strip-sigils f))
         (match stripped
           [`(defglobal ,_ ,_) stripped]
           [`(declare ,_ ,_ ,_) stripped]
           [`(extern ,_ ,_) stripped]
           [_ (transform-defun stripped)]))
       forms))

(define (parse-file path)
  (parse-forms
   (with-input-from-file path
     (lambda () (port->list read)))))
