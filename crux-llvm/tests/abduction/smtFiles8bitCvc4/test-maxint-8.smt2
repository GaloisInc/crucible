(set-option :print-success true)
; success
(set-option :produce-models true)
; success
(set-option :global-declarations true)
; success
(set-option :produce-unsat-cores true)
; success
(set-logic ALL_SUPPORTED)
; success
(get-info :error-behavior)
; (:error-behavior immediate-exit)
(push 1)
; success
(assert (! false :named x!0))
; success
(check-sat)
; unsat
(get-unsat-core)
; (
; x!0
; )
(pop 1)
; success
(exit)
; success
