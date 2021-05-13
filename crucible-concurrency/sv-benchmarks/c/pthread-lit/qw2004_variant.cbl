(defglobal $$stoppingFlag Bool)
(defglobal $$pendingIo Nat)
(defglobal $$stoppingEvent Nat)
(defglobal $$stopped Bool)

(defun @BCSP_IoIncrement () Bool
  (start start:
    (funcall @write_effect_set
      (vector-cons "$$pendingIo" (vector-cons "$$stoppingFlag" (vector))))
    (branch $$stoppingFlag stopped: incr:))

  (defblock stopped:
    (return #f))

  (defblock incr:
    (set-global! $$pendingIo (+ $$pendingIo 1))
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
    (funcall @BCSP_IoDecrement)
    (jump decr:))

  (defblock decr:
    (return ())))

(defun @BCSP_PnpStop ((_ Any)) Unit
  (start start:
    (funcall @write_effect "$$stoppingFlag")
    (set-global! $$stoppingFlag #t)
    (funcall @BCSP_IoDecrement)
    (funcall @read_effect "$$stoppingEvent")
    (branch (equal? $$stoppingEvent 1) stopping: notstopping:))
  (defblock stopping:
    (funcall @write_effect "$$stopped")
    (set-global! $$stopped #t)
    (return ()))
  (defblock notstopping:
    (return ())))

(defun @main () Unit
  (registers ($i Nat))
  (start start:
    (set-register! $i 0)
    (set-global! $$pendingIo 1)
    (set-global! $$stoppingFlag #f)
    (set-global! $$stoppingEvent 0)
    (set-global! $$stopped #f)

    (funcall @spawn @BCSP_PnpStop (to-any ()))
    (jump loop:))

  (defblock loop:
    (branch (< $i 2) spawn: done:))
  (defblock spawn:
    (funcall @spawn @BCSP_PnpAdd (to-any ()))
    (set-register! $i (+ 1 $i))
    (jump loop:))

  (defblock done:
    (return ())))
