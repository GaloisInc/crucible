#lang racket/base

(require redex/reduction-semantics)

(provide crucible-syntax)

(define-language crucible-syntax
  ;; Floating-point precisions
  (fp-prec Float Double Half Quad DoubleDouble X86-80)

  ;; Rounding modes
  (rm rne rna rtp rtn rtz)

  ;; String encodings
  (enc Unicode)

  ;; Types
  (ty Unit Bool Integer Nat Real Any
     (String enc)
     (Maybe ty)
     (Bitvector number)
     (FP fp-prec)
     (Ref ty)
     (Struct ty ...)
     (Variant ty ...)
     (Vector ty)
     (Sequence ty)
     (-> ty ... ty))

  ;; Names
  (x variable-not-otherwise-mentioned)
  (label variable-not-otherwise-mentioned)
  (fname variable-not-otherwise-mentioned)
  (reg variable-not-otherwise-mentioned)
  (gname variable-not-otherwise-mentioned)

  ;; Operator categories (for grouping typing rules)
  (numeric-varop + - *)
  (numeric-binop / mod)
  (numeric-cmpop < <=)
  (numeric-unop negate abs)
  (bool-varop and or xor)
  (bv-varop bv-xor bv-or bv-and)
  (bv-binop shl lshr ashr /$ smod)
  (bv-predop bv-carry bv-scarry bv-sborrow <$ <=$)
  (bv-extop zero-extend sign-extend)
  (fp-from-bvop ubv-to-fp sbv-to-fp)
  (fp-to-bvop fp-to-ubv fp-to-sbv)

  ;; Expressions
  (e unit-val
     #t #f
     number
     string
     x
     (the ty e)
     ;; arithmetic (polymorphic: numeric + bitvector)
     (numeric-varop e e e ...)
     (numeric-binop e e)
     ;; comparison
     (numeric-cmpop e e) (equal? e e)
     ;; unary numeric
     (numeric-unop e)
     ;; boolean
     (bool-varop e e e ...) (not e)
     (integer? e)
     ;; conditional
     (if e e e)
     ;; function call & reference
     (funcall fname e ...)
     (fun-ref fname)
     ;; string
     (string-concat e e) (show e) (fresh ty)
     (string-empty enc) (string-length e)
     ;; register & global
     (reg-ref reg) (global-ref gname)
     ;; Any
     (to-any e) (from-any ty e)
     ;; Maybe
     nothing (nothing ty) (just e) (from-just e e)
     ;; Bitvector
     (bv number number)
     (bv-varop e e e ...)
     (bv-binop e e) (bv-not e)
     (bool-to-bv number e)
     (bv-extop number e)
     (bv-concat e e) (bv-trunc number e)
     (bv-select number number e)
     (bv-nonzero e)
     (bv-predop e e)
     ;; Floating point
     (binary-to-fp fp-prec e) (fp-to-binary e)
     (fp-from-bvop fp-prec rm e)
     (fp-to-bvop number rm e)
     (fp-to-real e) (real-to-fp fp-prec rm e)
     ;; Reference
     (ref e) (deref e)
     ;; Struct
     (struct e ...)
     (get-field number e) (set-field e number e)
     ;; Variant
     (inj ty number e) (proj number e)
     ;; Vector
     (vector e ...) empty-vector (empty-vector ty)
     (vector-replicate e e)
     (vector-empty? e) (vector-size e)
     (vector-get e e) (vector-set e e e)
     (vector-cons e e)
     ;; Sequence
     seq-nil (seq-nil ty)
     (seq-cons e e) (seq-append e e)
     (seq-nil? e) (seq-length e)
     (seq-head e) (seq-tail e) (seq-uncons e))

  ;; Statements
  (s (let x e)
     (print e)
     (println e)
     (funcall fname e ...)
     (set-register! reg e)
     (set-global! gname e)
     (assert! e e)
     (assume! e e)
     (set-ref! e e)
     (drop-ref! e)
     (breakpoint string any))

  ;; Terminators
  (t (return e)
     (jump label)
     (branch e label label)
     (error e)
     (tail-call fname e ...)
     (output label e)
     (maybe-branch e label label)
     (case e label ...))

  ;; Blocks
  (block (start label s ... t)
         (defblock label s ... t)
         (defblock (label x ty) s ... t))

  ;; Functions
  (fundef (defun fname ((x ty) ...) ty block block ...)
          (defun fname ((x ty) ...) ty
            (registers (reg ty) ...) block block ...))

  ;; Top-level forms
  (top-form fundef
            (defglobal gname ty)
            (declare fname (ty ...) ty)
            (extern gname ty))

  ;; Programs
  (prog (top-form ...))

  ;; Environments (for typing)
  (V ((x ty) ...))
  (F ((fname (ty ...) ty) ...))
  (L any)
  (G ((gname ty) ...))
  (R ((reg ty) ...)))
