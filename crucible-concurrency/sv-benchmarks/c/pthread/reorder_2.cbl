;; This is reorder_2 or reorder_5 depending on # of setter or checker threads
;; i.e. 2/2 or 1/4
(defglobal $$a Integer)
(defglobal $$b Integer)

(defun @setThread ((_ Any)) Unit
  (start start:
    (funcall @write_effect "$$a")
    (set-global! $$a 1)
    (funcall @write_effect "$$b")
    (set-global! $$b -1)
    (return ())))

(defun @checkThread ((_ Any)) Unit
  (start start:
    (funcall @read_effect "$$a")
    (let a $$a)
    (funcall @read_effect "$$b")
    (let b $$b)
    (assert! (or (and (equal? a 0) (equal? b 0))
                 (and (equal? a 1) (equal? b -1))) "Incorrect")
    (return ())))

(defun @init_threads ((th (-> Any Unit)) (size Integer)) (Vector Integer)
  (registers
    ($ids (Vector Integer))
    ($i Integer))

  (start start:
    (set-register! $i 0)
    (set-register! $ids (vector))
    (jump loop:))

  (defblock loop:
    (let p (< $i size))
    (branch p body: done:))

  (defblock body:
    (let tid (funcall @spawn th (to-any ())))
    (set-register! $i (+ 1 $i))
    (set-register! $ids (vector-cons tid $ids))
    (jump loop:))

  (defblock done:
    (return $ids)))

(defun @join_vector ((thids (Vector Integer))) Unit
  (registers
    ($i Nat))

  (start start:
    (set-register! $i 0)
    (jump loop:))

  (defblock loop:
    (let p (< $i (vector-size thids)))
    (branch p body: done:))

  (defblock body:
    (funcall @join (vector-get thids $i))
    (set-register! $i (+ 1 $i))
    (jump loop:))

  (defblock done:
    (return ())))

(defun @main () Unit
  (start start:
    (set-global! $$a 0)
    (set-global! $$b 0)

    (let setters (funcall @init_threads @setThread 4))
    (let checkers (funcall @init_threads @checkThread 1))
    (funcall @join_vector setters)
    (funcall @join_vector checkers)

    (return ())))
