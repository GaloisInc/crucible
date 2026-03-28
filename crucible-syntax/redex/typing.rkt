#lang racket/base

(require redex/reduction-semantics
         racket/match
         racket/list
         racket/string
         "grammar.rkt")

(provide expr-synth expr-check stmt-ok term-ok
         stmts-ok block-ok blocks-ok defun-ok funs-ok prog-ok
         lookup fun-lookup reg-lookup global-lookup
         numeric? fp-width nth no-duplicates? label-env fun-env global-env)

;; --------------------------------------------------------------
;; Typing environments
;;
;;   F           — function signature environment
;;                 ((fname (ty_arg ...) ty_ret) ...)
;;                 Maps each function name to its argument types and return type.
;;
;;   L           — block label environment
;;                 ((label) ... (label ty) ...)
;;                 Maps each block label to nothing (plain jump target) or a
;;                 single parameter type (output/maybe-branch/case target).
;;
;;   G           — global variable environment
;;                 ((gname ty) ...)
;;                 Maps each global name to its type.
;;
;;   R           — register environment
;;                 ((reg ty) ...)
;;                 Maps each mutable register name (prefixed with $) to its type.
;;
;;   V           — local variable environment
;;                 ((x ty) ...)
;;                 Maps each let-bound or argument name to its type.
;;                 Extended by (let x e) statements; otherwise threaded unchanged.
;;
;;   ty           — a type (see grammar.rkt for the full ty non-terminal)
;;   ty_ret       — return type of the enclosing function

;; --------------------------------------------------------------
;; Variable lookup
(define-judgment-form crucible-syntax
  #:mode (lookup I I O)
  #:contract (lookup V x ty)

  [(lookup ((x_0 ty_0) ... (x ty) (x_1 ty_1) ...) x ty)
   (side-condition
    (not (member (term x) (term (x_0 ...)))))])

;; --------------------------------------------------------------
;; Function signature lookup
(define-judgment-form crucible-syntax
  #:mode (fun-lookup I I O O)
  #:contract (fun-lookup F fname (ty ...) ty)

  [(fun-lookup ((fname_0 (ty_a0 ...) ty_r0) ...
                (fname (ty_arg ...) ty_ret)
                (fname_1 (ty_a1 ...) ty_r1) ...)
               fname (ty_arg ...) ty_ret)
   (side-condition
    (not (member (term fname) (term (fname_0 ...)))))])

;; --------------------------------------------------------------
;; Register lookup
(define-judgment-form crucible-syntax
  #:mode (reg-lookup I I O)
  #:contract (reg-lookup R reg ty)

  [(reg-lookup ((reg_0 ty_0) ... (reg ty) (reg_1 ty_1) ...) reg ty)
   (side-condition
    (not (member (term reg) (term (reg_0 ...)))))])

;; --------------------------------------------------------------
;; Global lookup
(define-judgment-form crucible-syntax
  #:mode (global-lookup I I O)
  #:contract (global-lookup G gname ty)

  [(global-lookup
    ((gname_0 ty_0) ... (gname ty) (gname_1 ty_1) ...) gname ty)
   (side-condition
    (not (member (term gname) (term (gname_0 ...)))))])

;; --------------------------------------------------------------
;; Metafunctions

(define-metafunction crucible-syntax
  numeric? : ty -> any
  [(numeric? Integer) #t]
  [(numeric? Nat)     #t]
  [(numeric? Real)    #t]
  [(numeric? (Bitvector number)) #t]
  [(numeric? ty)       #f])

(define-metafunction crucible-syntax
  fp-width : fp-prec -> number
  [(fp-width Half)         16]
  [(fp-width Float)        32]
  [(fp-width Double)       64]
  [(fp-width X86-80)       80]
  [(fp-width Quad)        128]
  [(fp-width DoubleDouble) 128])

(define-metafunction crucible-syntax
  nth : (ty ...) number -> ty
  [(nth (ty_0 ty_rest ...) 0) ty_0]
  [(nth (ty_0 ty_rest ...) number)
   (nth (ty_rest ...) ,(sub1 (term number)))
   (side-condition (> (term number) 0))])

(define-metafunction crucible-syntax
  no-duplicates? : (x ...) -> any
  [(no-duplicates? ()) #t]
  [(no-duplicates? (x_0 x_rest ...))
   #f
   (side-condition (member (term x_0) (term (x_rest ...))))]
  [(no-duplicates? (x_0 x_rest ...))
   (no-duplicates? (x_rest ...))])

;; Racket helpers

(define (label-in-lambda? L lbl)
  (for/or ([entry (in-list L)])
    (and (= (length entry) 1) (equal? (car entry) lbl))))

(define (param-label-type L lbl)
  (for/or ([entry (in-list L)])
    (and (= (length entry) 2)
         (equal? (car entry) lbl)
         (cadr entry))))

;; Well-formedness helper for defun-ok side-condition
(define (all-regs-prefixed? regs)
  (for/and ([r (in-list regs)])
    (string-prefix? (symbol->string r) "$")))

;; Check all expressions in `es` against type `ty` (checking mode)
(define (check-all-check F G R V es ty)
  (for/and ([e (in-list es)])
    (judgment-holds (expr-check ,F ,G ,R ,V ,e ,ty))))

;; Check expressions against corresponding types (zipped)
(define (check-args F G R V es tys)
  (and (= (length es) (length tys))
       (for/and ([e (in-list es)]
                 [ty (in-list tys)])
         (judgment-holds (expr-check ,F ,G ,R ,V ,e ,ty)))))

;; Check case labels match variant types
(define (check-case-labels L labels variant-types)
  (and (= (length labels) (length variant-types))
       (for/and ([lbl (in-list labels)]
                 [ty (in-list variant-types)])
         (equal? (param-label-type L lbl) ty))))

;; --------------------------------------------------------------
;; Expression typing (bidirectional)

;; Synthesis mode: infer type from expression
(define-judgment-form crucible-syntax
  #:mode (expr-synth I I I I I O)
  #:contract (expr-synth F G R V e ty)

  ;; unit
  [(expr-synth F G R V unit-val Unit)]

  ;; booleans
  [(expr-synth F G R V #t Bool)]
  [(expr-synth F G R V #f Bool)]

  ;; integer literals → Integer
  [(expr-synth F G R V number Integer)
   (where #t ,(exact-integer? (term number)))]

  ;; non-negative integer literals → Nat
  [(expr-synth F G R V number Nat)
   (where #t ,(and (exact-integer? (term number))
                   (>= (term number) 0)))]

  ;; exact numeric literals → Real
  [(expr-synth F G R V number Real)
   (where #t ,(exact? (term number)))]

  ;; string literals
  [(expr-synth F G R V string (String Unicode))
   (where #t ,(string? (term string)))]

  ;; variable
  [(expr-synth F G R V x ty)
   (lookup V x ty)]

  ;; type ascription
  [(expr-synth F G R V (the ty e) ty)
   (expr-check F G R V e ty)]

  ;; --- Arithmetic (variadic 2+, polymorphic numeric) ---
  [(expr-synth F G R V (numeric-varop e_1 e_2 e_rest ...) ty)
   (expr-synth F G R V e_1 ty)
   (expr-check F G R V e_2 ty)
   (side-condition
    ,(check-all-check (term F) (term G) (term R)
                      (term V) (term (e_rest ...)) (term ty)))
   (where #t (numeric? ty))]

  ;; --- Arithmetic (binary, polymorphic numeric) ---
  [(expr-synth F G R V (numeric-binop e_1 e_2) ty)
   (expr-synth F G R V e_1 ty)
   (expr-check F G R V e_2 ty)
   (where #t (numeric? ty))]

  ;; --- Numeric comparisons → Bool ---
  [(expr-synth F G R V (numeric-cmpop e_1 e_2) Bool)
   (expr-synth F G R V e_1 ty)
   (expr-check F G R V e_2 ty)
   (where #t (numeric? ty))]

  ;; equality (fully polymorphic)
  [(expr-synth F G R V (equal? e_1 e_2) Bool)
   (expr-synth F G R V e_1 ty)
   (expr-check F G R V e_2 ty)]

  ;; --- Unary numeric ---
  [(expr-synth F G R V (numeric-unop e) ty)
   (expr-synth F G R V e ty)
   (where #t (numeric? ty))]

  ;; --- Boolean ops (variadic 2+) ---
  [(expr-synth F G R V (bool-varop e_1 e_2 e_rest ...) Bool)
   (expr-check F G R V e_1 Bool)
   (expr-check F G R V e_2 Bool)
   (side-condition
    ,(check-all-check (term F) (term G) (term R)
                      (term V) (term (e_rest ...)) 'Bool))]

  [(expr-synth F G R V (not e_1) Bool)
   (expr-check F G R V e_1 Bool)]

  ;; integer?
  [(expr-synth F G R V (integer? e) Bool)
   (expr-check F G R V e Real)]

  ;; conditional
  [(expr-synth F G R V (if e_c e_t e_f) ty)
   (expr-check F G R V e_c Bool)
   (expr-synth F G R V e_t ty)
   (expr-check F G R V e_f ty)]

  ;; --- Function call & reference ---

  [(expr-synth F G R V (funcall fname e ...) ty_ret)
   (fun-lookup F fname (ty_arg ...) ty_ret)
   (side-condition ,(check-args (term F) (term G) (term R) (term V)
                                (term (e ...)) (term (ty_arg ...))))]

  [(expr-synth F G R V (funcall fname e ...) ty_ret)
   (lookup V fname (-> ty_arg ... ty_ret))
   (side-condition ,(check-args (term F) (term G) (term R) (term V)
                                (term (e ...)) (term (ty_arg ...))))]

  [(expr-synth F G R V (fun-ref fname) (-> ty_arg ... ty_ret))
   (fun-lookup F fname (ty_arg ...) ty_ret)]

  ;; --- String ops ---

  [(expr-synth F G R V (string-concat e_1 e_2) (String Unicode))
   (expr-check F G R V e_1 (String Unicode))
   (expr-check F G R V e_2 (String Unicode))]

  [(expr-synth F G R V (show e) (String Unicode))
   (expr-synth F G R V e ty)]

  [(expr-synth F G R V (fresh ty) ty)]

  [(expr-synth F G R V (string-empty enc) (String enc))]

  [(expr-synth F G R V (string-length e) Nat)
   (expr-synth F G R V e (String enc))]

  ;; --- Register & global ---

  [(expr-synth F G R V (reg-ref reg) ty)
   (reg-lookup R reg ty)]

  [(expr-synth F G R V (global-ref gname) ty)
   (global-lookup G gname ty)]

  ;; --- Any ---

  [(expr-synth F G R V (to-any e) Any)
   (expr-synth F G R V e ty)]

  [(expr-synth F G R V (from-any ty e) (Maybe ty))
   (expr-check F G R V e Any)]

  ;; --- Maybe ---

  [(expr-synth F G R V (nothing ty) (Maybe ty))]

  [(expr-synth F G R V (just e) (Maybe ty))
   (expr-synth F G R V e ty)]

  [(expr-synth F G R V (from-just e_1 e_2) ty)
   (expr-synth F G R V e_1 (Maybe ty))
   (expr-check F G R V e_2 (String Unicode))]

  ;; --- Bitvector ---

  ;; literal
  [(expr-synth F G R V (bv number_w number_v) (Bitvector number_w))
   (where #t ,(and (exact-integer? (term number_w))
                   (> (term number_w) 0)))]

  ;; variadic bitwise ops (2+)
  [(expr-synth F G R V (bv-varop e_1 e_2 e_rest ...) (Bitvector number))
   (expr-synth F G R V e_1 (Bitvector number))
   (expr-check F G R V e_2 (Bitvector number))
   (side-condition
    ,(check-all-check
      (term F) (term G) (term R) (term V)
      (term (e_rest ...)) (term (Bitvector number))))]

  ;; binary same-width ops
  [(expr-synth F G R V (bv-binop e_1 e_2) (Bitvector number))
   (expr-synth F G R V e_1 (Bitvector number))
   (expr-check F G R V e_2 (Bitvector number))]

  ;; binary predicates → Bool
  [(expr-synth F G R V (bv-predop e_1 e_2) Bool)
   (expr-synth F G R V e_1 (Bitvector number))
   (expr-check F G R V e_2 (Bitvector number))]

  ;; bv-not (unary)
  [(expr-synth F G R V (bv-not e) (Bitvector number))
   (expr-synth F G R V e (Bitvector number))]

  ;; bool-to-bv
  [(expr-synth F G R V (bool-to-bv number e) (Bitvector number))
   (expr-check F G R V e Bool)]

  ;; extend (target must be larger)
  [(expr-synth F G R V (bv-extop number_n e) (Bitvector number_n))
   (expr-synth F G R V e (Bitvector number_m))
   (where #t ,(> (term number_n) (term number_m)))]

  ;; concat
  [(expr-synth F G R V (bv-concat e_1 e_2) (Bitvector number_sum))
   (expr-synth F G R V e_1 (Bitvector number_1))
   (expr-synth F G R V e_2 (Bitvector number_2))
   (where number_sum ,(+ (term number_1) (term number_2)))]

  ;; truncate (target must be smaller)
  [(expr-synth F G R V (bv-trunc number_n e) (Bitvector number_n))
   (expr-synth F G R V e (Bitvector number_m))
   (where #t ,(< (term number_n) (term number_m)))]

  ;; select (offset + width must fit in source)
  [(expr-synth F G R V
     (bv-select number_off number_w e) (Bitvector number_w))
   (expr-synth F G R V e (Bitvector number_m))
   (where #t ,(<= (+ (term number_off) (term number_w))
                   (term number_m)))]

  ;; bv-nonzero
  [(expr-synth F G R V (bv-nonzero e) Bool)
   (expr-synth F G R V e (Bitvector number))]

  ;; --- Floating point ---

  [(expr-synth F G R V (binary-to-fp fp-prec e) (FP fp-prec))
   (expr-synth F G R V e (Bitvector number))]

  [(expr-synth F G R V (fp-to-binary e) (Bitvector number_w))
   (expr-synth F G R V e (FP fp-prec))
   (where number_w (fp-width fp-prec))]

  ;; BV → FP conversions
  [(expr-synth F G R V (fp-from-bvop fp-prec rm e) (FP fp-prec))
   (expr-synth F G R V e (Bitvector number))]

  ;; FP → BV conversions
  [(expr-synth F G R V (fp-to-bvop number rm e) (Bitvector number))
   (expr-synth F G R V e (FP fp-prec))]

  [(expr-synth F G R V (fp-to-real e) Real)
   (expr-synth F G R V e (FP fp-prec))]

  [(expr-synth F G R V (real-to-fp fp-prec rm e) (FP fp-prec))
   (expr-check F G R V e Real)]

  ;; --- Reference ---

  [(expr-synth F G R V (ref e) (Ref ty))
   (expr-synth F G R V e ty)]

  [(expr-synth F G R V (deref e) ty)
   (expr-synth F G R V e (Ref ty))]

  ;; --- Struct ---

  [(expr-synth F G R V (struct e ...) (Struct ty ...))
   (expr-synth F G R V e ty) ...]

  [(expr-synth F G R V (get-field number e) ty_n)
   (expr-synth F G R V e (Struct ty ...))
   (where ty_n (nth (ty ...) number))]

  [(expr-synth F G R V (set-field e_1 number e_2) (Struct ty ...))
   (expr-synth F G R V e_1 (Struct ty ...))
   (where ty_n (nth (ty ...) number))
   (expr-check F G R V e_2 ty_n)]

  ;; --- Variant ---

  [(expr-synth F G R V (inj ty_var number e) ty_var)
   (where (Variant ty ...) ty_var)
   (where ty_n (nth (ty ...) number))
   (expr-check F G R V e ty_n)]

  [(expr-synth F G R V (proj number e) (Maybe ty_n))
   (expr-synth F G R V e (Variant ty ...))
   (where ty_n (nth (ty ...) number))]

  ;; --- Vector ---

  [(expr-synth F G R V (empty-vector ty) (Vector ty))]

  [(expr-synth F G R V (vector e_1 e_rest ...) (Vector ty))
   (expr-synth F G R V e_1 ty)
   (side-condition
    ,(check-all-check (term F) (term G) (term R)
                      (term V) (term (e_rest ...)) (term ty)))]

  [(expr-synth F G R V (vector-replicate e_1 e_2) (Vector ty))
   (expr-check F G R V e_1 Nat)
   (expr-synth F G R V e_2 ty)]

  [(expr-synth F G R V (vector-empty? e) Bool)
   (expr-synth F G R V e (Vector ty))]

  [(expr-synth F G R V (vector-size e) Nat)
   (expr-synth F G R V e (Vector ty))]

  [(expr-synth F G R V (vector-get e_1 e_2) ty)
   (expr-synth F G R V e_1 (Vector ty))
   (expr-check F G R V e_2 Nat)]

  [(expr-synth F G R V (vector-set e_1 e_2 e_3) (Vector ty))
   (expr-synth F G R V e_1 (Vector ty))
   (expr-check F G R V e_2 Nat)
   (expr-check F G R V e_3 ty)]

  [(expr-synth F G R V (vector-cons e_1 e_2) (Vector ty))
   (expr-synth F G R V e_1 ty)
   (expr-check F G R V e_2 (Vector ty))]

  ;; --- Sequence ---

  [(expr-synth F G R V (seq-nil ty) (Sequence ty))]

  [(expr-synth F G R V (seq-cons e_1 e_2) (Sequence ty))
   (expr-synth F G R V e_1 ty)
   (expr-check F G R V e_2 (Sequence ty))]

  [(expr-synth F G R V (seq-append e_1 e_2) (Sequence ty))
   (expr-synth F G R V e_1 (Sequence ty))
   (expr-check F G R V e_2 (Sequence ty))]

  [(expr-synth F G R V (seq-nil? e) Bool)
   (expr-synth F G R V e (Sequence ty))]

  [(expr-synth F G R V (seq-length e) Nat)
   (expr-synth F G R V e (Sequence ty))]

  [(expr-synth F G R V (seq-head e) (Maybe ty))
   (expr-synth F G R V e (Sequence ty))]

  [(expr-synth F G R V (seq-tail e) (Maybe (Sequence ty)))
   (expr-synth F G R V e (Sequence ty))]

  [(expr-synth F G R V (seq-uncons e) (Maybe (Struct ty (Sequence ty))))
   (expr-synth F G R V e (Sequence ty))])

;; --------------------------------------------------------------
;; Checking mode: verify expression against expected type
(define-judgment-form crucible-syntax
  #:mode (expr-check I I I I I I)
  #:contract (expr-check F G R V e ty)

  ;; Bare empty constructors work when checking against the right type
  [(expr-check F G R V nothing (Maybe ty))]

  [(expr-check F G R V seq-nil (Sequence ty))]

  [(expr-check F G R V empty-vector (Vector ty))]

  ;; Type ascription in checking mode
  [(expr-check F G R V (the ty e) ty)
   (expr-check F G R V e ty)]

  ;; Subsumption: can always check by synthesizing and verifying match
  ;; This must be LAST to allow more specific rules to match first
  [(expr-check F G R V e ty)
   (expr-synth F G R V e ty)])


;; --------------------------------------------------------------
;; Statement typing (extends V)
(define-judgment-form crucible-syntax
  #:mode (stmt-ok I I I I I I O)
  #:contract (stmt-ok F L G R V s V)

  ;; let (no duplicate bindings)
  [(stmt-ok F L G R
     ((x_prev ty_prev) ...) (let x e) ((x ty) (x_prev ty_prev) ...))
   (side-condition ,(not (member (term x) (term (x_prev ...)))))
   (expr-synth F G R ((x_prev ty_prev) ...) e ty)]

  ;; print (V unchanged)
  [(stmt-ok F L G R V (print e) V)
   (expr-synth F G R V e ty)]

  ;; println (V unchanged, String only)
  [(stmt-ok F L G R V (println e) V)
   (expr-check F G R V e (String Unicode))]

  ;; funcall as statement (V unchanged, result discarded)
  [(stmt-ok F L G R V (funcall fname e ...) V)
   (fun-lookup F fname (ty_arg ...) ty_ret)
   (side-condition ,(check-args (term F) (term G) (term R) (term V)
                                (term (e ...)) (term (ty_arg ...))))]

  [(stmt-ok F L G R V (funcall fname e ...) V)
   (lookup V fname (-> ty_arg ... ty_ret))
   (side-condition ,(check-args (term F) (term G) (term R) (term V)
                                (term (e ...)) (term (ty_arg ...))))]

  ;; set-register! (V unchanged)
  [(stmt-ok F L G R V (set-register! reg e) V)
   (reg-lookup R reg ty)
   (expr-check F G R V e ty)]

  ;; set-global! (V unchanged)
  [(stmt-ok F L G R V (set-global! gname e) V)
   (global-lookup G gname ty)
   (expr-check F G R V e ty)]

  ;; assert! (Bool × String, V unchanged)
  [(stmt-ok F L G R V (assert! e_cond e_msg) V)
   (expr-check F G R V e_cond Bool)
   (expr-check F G R V e_msg (String Unicode))]

  ;; assume! (Bool × String, V unchanged)
  [(stmt-ok F L G R V (assume! e_cond e_msg) V)
   (expr-check F G R V e_cond Bool)
   (expr-check F G R V e_msg (String Unicode))]

  ;; set-ref! (V unchanged)
  [(stmt-ok F L G R V (set-ref! e_ref e_val) V)
   (expr-synth F G R V e_ref (Ref ty))
   (expr-check F G R V e_val ty)]

  ;; drop-ref! (V unchanged)
  [(stmt-ok F L G R V (drop-ref! e) V)
   (expr-synth F G R V e (Ref ty))]

  ;; breakpoint (V unchanged, just check label is string)
  [(stmt-ok F L G R V (breakpoint string any) V)
   (where #t ,(string? (term string)))])

;; --------------------------------------------------------------
;; Terminator typing
(define-judgment-form crucible-syntax
  #:mode (term-ok I I I I I I I)
  #:contract (term-ok F L G R V ty t)

  ;; return
  [(term-ok F L G R V ty_ret (return e))
   (expr-check F G R V e ty_ret)]

  ;; jump
  [(term-ok F L G R V ty_ret (jump label))
   (where #t ,(label-in-lambda? (term L) (term label)))]

  ;; branch
  [(term-ok F L G R V ty_ret (branch e label_1 label_2))
   (expr-check F G R V e Bool)
   (where #t ,(label-in-lambda? (term L) (term label_1)))
   (where #t ,(label-in-lambda? (term L) (term label_2)))]

  ;; error
  [(term-ok F L G R V ty_ret (error e))
   (expr-check F G R V e (String Unicode))]

  ;; tail-call (direct function name)
  [(term-ok F L G R V ty_ret (tail-call fname e ...))
   (fun-lookup F fname (ty_arg ...) ty_ret)
   (side-condition ,(check-args (term F) (term G) (term R) (term V)
                                (term (e ...)) (term (ty_arg ...))))]

  ;; tail-call (variable with function type)
  [(term-ok F L G R V ty_ret (tail-call fname e ...))
   (lookup V fname (-> ty_arg ... ty_ret))
   (side-condition ,(check-args (term F) (term G) (term R) (term V)
                                (term (e ...)) (term (ty_arg ...))))]

  ;; output (jump to parameterized block)
  [(term-ok F L G R V ty_ret (output label e))
   (where ty_p ,(param-label-type (term L) (term label)))
   (expr-check F G R V e ty_p)]

  ;; maybe-branch
  [(term-ok F L G R V ty_ret
     (maybe-branch e label_j label_n))
   (where ty_p
     ,(param-label-type (term L) (term label_j)))
   (expr-check F G R V e (Maybe ty_p))
   (where #t ,(label-in-lambda? (term L) (term label_n)))]

  ;; case (variant dispatch)
  [(term-ok F L G R V ty_ret (case e label ...))
   (expr-synth F G R V e (Variant ty_v ...))
   (where #t
     ,(check-case-labels
       (term L) (term (label ...)) (term (ty_v ...))))])

;; --------------------------------------------------------------
;; Statement sequence typing (threads V through a list of statements)
(define-judgment-form crucible-syntax
  #:mode (stmts-ok I I I I I I O)
  #:contract (stmts-ok F L G R V (s ...) V)

  ;; Base: empty list
  [(stmts-ok F L G R V () V)]

  ;; Inductive: check head, thread V
  [(stmts-ok F L G R V (s_0 s_rest ...) V_final)
   (stmt-ok F L G R V s_0 V_1)
   (stmts-ok F L G R V_1 (s_rest ...) V_final)])

;; --------------------------------------------------------------
;; Label environment extraction from a block list
(define-metafunction crucible-syntax
  label-env : (block ...) -> any

  [(label-env ()) ()]
  [(label-env ((defblock (label x ty) s ... t) block_rest ...))
   ((label ty) any_rest ...)
   (where (any_rest ...) (label-env (block_rest ...)))]
  [(label-env ((start label s ... t) block_rest ...))
   ((label) any_rest ...)
   (where (any_rest ...) (label-env (block_rest ...)))]
  [(label-env ((defblock label s ... t) block_rest ...))
   ((label) any_rest ...)
   (where (any_rest ...) (label-env (block_rest ...)))])

;; --------------------------------------------------------------
;; Block typing
(define-judgment-form crucible-syntax
  #:mode (block-ok I I I I I I I O)
  #:contract (block-ok F L G R V ty block V)

  ;; start block
  [(block-ok F L G R V ty_ret (start label s ... t) V_final)
   (stmts-ok F L G R V (s ...) V_final)
   (term-ok F L G R V_final ty_ret t)]

  ;; plain defblock
  [(block-ok F L G R V ty_ret (defblock label s ... t) V_final)
   (stmts-ok F L G R V (s ...) V_final)
   (term-ok F L G R V_final ty_ret t)]

  ;; parameterized defblock — extends V with the block parameter
  [(block-ok F L G R ((x_v ty_v) ...) ty_ret
     (defblock (label x_p ty_p) s ... t) V_final)
   (stmts-ok F L G R ((x_p ty_p) (x_v ty_v) ...) (s ...) V_final)
   (term-ok F L G R V_final ty_ret t)])

;; --------------------------------------------------------------
;; Block list typing (threads V across blocks)
(define-judgment-form crucible-syntax
  #:mode (blocks-ok I I I I I I I)
  #:contract (blocks-ok F L G R V ty (block ...))

  [(blocks-ok F L G R V ty_ret ())]

  [(blocks-ok F L G R V ty_ret (block_0 block_rest ...))
   (block-ok F L G R V ty_ret block_0 V_1)
   (blocks-ok F L G R V_1 ty_ret (block_rest ...))])

;; --------------------------------------------------------------
;; Function typing
(define-judgment-form crucible-syntax
  #:mode (defun-ok I I I)
  #:contract (defun-ok F G fundef)

  ;; Without registers
  [(defun-ok F G
     (defun fname ((x ty_arg) ...) ty_ret
       (start label_0 s_0 ... t_0) block_rest ...))
   (where #t (no-duplicates? (x ...)))
   (where L (label-env ((start label_0 s_0 ... t_0) block_rest ...)))
   (blocks-ok F L G () ((x ty_arg) ...) ty_ret
     ((start label_0 s_0 ... t_0) block_rest ...))]

  ;; With registers
  [(defun-ok F G
     (defun fname ((x ty_arg) ...) ty_ret
       (registers (reg ty_reg) ...)
       (start label_0 s_0 ... t_0) block_rest ...))
   (where #t (no-duplicates? (x ...)))
   (side-condition ,(all-regs-prefixed? (term (reg ...))))
   (where L (label-env ((start label_0 s_0 ... t_0) block_rest ...)))
   (blocks-ok F L G ((reg ty_reg) ...) ((x ty_arg) ...) ty_ret
     ((start label_0 s_0 ... t_0) block_rest ...))])

;; --------------------------------------------------------------
;; Environment extraction metafunctions

(define-metafunction crucible-syntax
  fun-env : (top-form ...) -> F

  [(fun-env ()) ()]
  [(fun-env ((defun fname ((x ty_arg) ...) ty_ret any_body ...) top-form_rest ...))
   ((fname (ty_arg ...) ty_ret) any_F ...)
   (where (any_F ...) (fun-env (top-form_rest ...)))]
  [(fun-env ((declare fname (ty_arg ...) ty_ret) top-form_rest ...))
   ((fname (ty_arg ...) ty_ret) any_F ...)
   (where (any_F ...) (fun-env (top-form_rest ...)))]
  [(fun-env (top-form_0 top-form_rest ...))
   (fun-env (top-form_rest ...))])

(define-metafunction crucible-syntax
  global-env : (top-form ...) -> G

  [(global-env ()) ()]
  [(global-env ((defglobal gname ty) top-form_rest ...))
   ((gname ty) any_G ...)
   (where (any_G ...) (global-env (top-form_rest ...)))]
  [(global-env ((extern gname ty) top-form_rest ...))
   ((gname ty) any_G ...)
   (where (any_G ...) (global-env (top-form_rest ...)))]
  [(global-env (top-form_0 top-form_rest ...))
   (global-env (top-form_rest ...))])

;; --------------------------------------------------------------
;; Function list typing
(define-judgment-form crucible-syntax
  #:mode (funs-ok I I I)
  #:contract (funs-ok F G (top-form ...))

  [(funs-ok F G ())]

  ;; defun — check it, continue
  [(funs-ok F G (fundef_0 top-form_rest ...))
   (defun-ok F G fundef_0)
   (funs-ok F G (top-form_rest ...))]

  ;; non-defun — skip
  [(funs-ok F G (top-form_0 top-form_rest ...))
   (side-condition ,(not (and (pair? (term top-form_0))
                              (eq? 'defun (car (term top-form_0))))))
   (funs-ok F G (top-form_rest ...))])

;; --------------------------------------------------------------
;; Program typing
(define-judgment-form crucible-syntax
  #:mode (prog-ok I)
  #:contract (prog-ok prog)

  [(prog-ok (top-form ...))
   (where F (fun-env (top-form ...)))
   (where G (global-env (top-form ...)))
   (funs-ok F G (top-form ...))])
