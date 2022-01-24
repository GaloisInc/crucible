(defglobal $$stoppingFlag Bool)
(defglobal $$pendingIo Nat)
(defglobal $$stoppingEvent Nat)
(defglobal $$stopped Bool)

(defun @BCSP_IoIncrement () Bool
  (start start:
    (funcall @write_effect_set (vector-cons "$$stoppingFlag" (vector-cons "$$pendingIo" (vector))))
    (let lsf $$stoppingFlag)
    (branch lsf stopped: incr:))

  (defblock stopped:
    (return #f))

  (defblock incr:
    (let lp $$pendingIo)
    (set-global! $$pendingIo (+ lp 1))
    (return #t)))

(defun @dec () Nat
  (start start:
    (funcall @write_effect "$$pendingIo")
    (set-global! $$pendingIo (- $$pendingIo 1))
    (return $$pendingIo)))

(defun @BCSP_IoDecrement () Unit
  (start start:
    (let pending (funcall @dec))
    (branch (equal? 0 pending) stop: no_stop:))

  (defblock stop:
    (funcall @write_effect "$$stoppingEvent")
    (set-global! $$stoppingEvent 1)
    (return ()))

  (defblock no_stop:
    (return ())))

(defun @BCSP_PnpAdd ((_ Any)) Unit
  (start start:
    (let status (funcall @BCSP_IoIncrement))
    (branch status not_stopped: decr:))

  (defblock not_stopped:
    (funcall @read_effect "$$stopped")
    (assert! (not $$stopped) "Not Stopped")
    (jump decr:))

  (defblock decr:
    (funcall @BCSP_IoDecrement)
    (return ())))

(defun @BCSP_PnpStop ((_ Any)) Unit
  (start start:
    (funcall @write_effect "$$stoppingFlag")
    (set-global! $$stoppingFlag #t)
    (funcall @BCSP_IoDecrement)
    (funcall @read_effect "$$stoppingEvent")
    (assume! (equal? $$stoppingEvent 1) "Uh")
    (funcall @write_effect "$$stopped")
    (set-global! $$stopped #t)
    (return ())))

(defun @main () Unit
  (start start:
    (set-global! $$pendingIo 1)
    (set-global! $$stoppingFlag #f)
    (set-global! $$stoppingEvent 0)
    (set-global! $$stopped #f)

    (funcall @spawn @BCSP_PnpStop (to-any ()))
    (funcall @BCSP_PnpAdd (to-any ()))
    (return ())))
