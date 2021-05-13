(defglobal $$CNT Nat)

(defglobal $$thread_count1 Integer)
(defglobal $$seen1 Integer)

(defglobal $$thread_count2 Integer)
(defglobal $$seen2 Integer)

(defglobal $$pre (Vector Bool))
(defglobal $$in (Vector Bool))
(defglobal $$post (Vector Bool))
(defglobal $$sig1 (Vector Bool))
(defglobal $$sig2 (Vector Bool))

(defun @barriers_init ((count Integer)) Unit
  (start start:
    (set-global! $$thread_count1 count)
    (set-global! $$seen1 0)

    (set-global! $$thread_count2 count)
    (set-global! $$seen2 0)
    (return ())))

(defun @barrier1_wait () Bool
  (start start:
    (assert! (< $$seen1 $$thread_count1) "Wait on used barrier!")
    (funcall @write_effect "barrier_lock1")
    (set-global! $$seen1 (+ $$seen1 1))
    (branch (equal? $$seen1 $$thread_count1) broadcast: wait:))

  (defblock broadcast:
    (funcall @cond_signal "signal1")
    (return #t))

  (defblock wait:
    (funcall @cond_wait "signal1" "barrier_lock1")
    (branch (< $$seen1 $$thread_count1) wait: done:))

  (defblock done:
    (return #f)))

(defun @barrier2_wait () Bool
  (start start:
    (assert! (< $$seen2 $$thread_count2) "Wait on used barrier!")
    (funcall @write_effect "barrier_lock2")
    (set-global! $$seen2 (+ $$seen2 1))
    (branch (equal? $$seen2 $$thread_count2) broadcast: wait:))

  (defblock broadcast:
    (funcall @cond_signal "signal2")
    (return #t))

  (defblock wait:
    (funcall @cond_wait "signal2" "barrier_lock2")
    (branch (< $$seen2 $$thread_count2) wait: done:))

  (defblock done:
    (return #f)))

(defun @worker ((arg Any)) Unit
  (registers ($i Nat) ($sig Nat))

  (start start:
    (let tid (from-just (from-any Nat arg) "Cast input"))

    ;; pre[tid] = true;
    (let tidstr (show tid))
    (let str (string-concat "$$pre" tidstr))
    (funcall @write_effect str)
    (set-global! $$pre (vector-set $$pre tid #t))

    (set-register! $i 0)
    (jump loop1:))

  (defblock loop1:
    (branch (< $i $$CNT) loop1_body: loop1_post:))
  (defblock loop1_body:
    ;; assert !in[i]
    (funcall @read_effect (string-concat "$$in" (show $i)))
    (assert! (not (vector-get $$in $i)) "not in")
    ;; assert !post[i]
    (funcall @read_effect (string-concat "$$post" (show $i)))
    (assert! (not (vector-get $$post $i)) "not post")
    (set-register! $i (+ $i 1))
    (jump loop1:))

  (defblock loop1_post:
    ;; sig1[tid] = barrier_wait(b1);
    (let res (funcall @barrier1_wait))
    (funcall @write_effect (string-concat "$$sig1" (show tid)))
    (set-global! $$sig1 (vector-set $$sig1 tid res))

    (set-register! $sig 0)
    (set-register! $i 0)
    (jump loop2:))

  (defblock loop2:
    (branch (< $i $$CNT) loop2_body: loop2_post:))
  (defblock loop2_body:
    ;; assert pre[i]
    (funcall @read_effect (string-concat "$$pre" (show $i)))
    (assert! (vector-get $$pre $i) "not pre")
    ;; sig += sig1[i]
    (funcall @read_effect (string-concat "$$sig1" (show $i)))
    (set-register! $sig (+ $sig (if (vector-get $$sig1 $i) 1 0)))

    (set-register! $i (+ $i 1))
    (jump loop2:))

  (defblock loop2_post:
    ;; assert(sig <= 1)
    (assert! (<= $sig 1) "Barrier wait returns true only once!")

    ;; assert(!in[tid])
    (funcall @read_effect (string-concat "$$in" (show tid)))
    (assert! (not (vector-get $$in tid)) "Not in yet")

    ;; in[tid] = true
    (funcall @write_effect (string-concat "$$in" (show tid)))
    (set-global! $$in (vector-set $$in tid #t))

    ;; sig2[tid] = barrier_wait(barrier2);
    (let res1 (funcall @barrier1_wait)) ;; This is the bug, should be barrier2_wait
    (funcall @write_effect (string-concat "$$sig2" (show tid)))
    (set-global! $$sig2 (vector-set $$sig2 tid res1))

    ;; assert (!post[tid]);
    (funcall @read_effect (string-concat "$$post" (show tid)))
    (assert! (not (vector-get $$post tid)) "not in post yet")

    ;; post[tid] = true
    (funcall @write_effect (string-concat "$$post" (show tid)))
    (set-global! $$post (vector-set $$post tid #t))

    (set-register! $i 0)
    (set-register! $sig 0)
    (jump loop3:))

  (defblock loop3:
    (branch (< $i $$CNT) loop3_body: loop3_post:))
  (defblock loop3_body:
    ;; assert pre[i]
    (funcall @read_effect (string-concat "$$pre" (show $i)))
    (assert! (vector-get $$pre $i) "pre")
    ;; assert in[i]
    (funcall @read_effect (string-concat "$$in" (show $i)))
    (assert! (vector-get $$in $i) "in")
    ;; sig += sig1[i]
    (funcall @read_effect (string-concat "$$sig1" (show $i)))
    (set-register! $sig (+ $sig (if (vector-get $$sig1 $i) 1 0)))

    (set-register! $i (+ $i 1))
    (jump loop3:))

  (defblock loop3_post:
    (assert! (equal? $sig 1) "After second barrier, sig1 is set for everyone")
    (set-register! $i 0)
    (set-register! $sig 0)
    (jump loop4:))

  (defblock loop4:
    (branch (< $i $$CNT) loop4_body: loop4_post:))
  (defblock loop4_body:
    ;; sig += sig2[i]
    (funcall @read_effect (string-concat "$$sig2" (show $i)))
    (set-register! $sig (+ $sig (if (vector-get $$sig2 $i) 1 0)))

    (set-register! $i (+ $i 1))
    (jump loop4:))

  (defblock loop4_post:
    (assert! (<= $sig 1) "Only one thread gets #t from barrier")
    (return ())))

(defun @main () Unit
  (start start:
    (set-global! $$CNT 2)
    (funcall @barriers_init 2)

    (set-global! $$pre  (vector-replicate $$CNT #f))
    (set-global! $$in   (vector-replicate $$CNT #f))
    (set-global! $$post (vector-replicate $$CNT #f))
    (set-global! $$sig1 (vector-replicate $$CNT #f))
    (set-global! $$sig2 (vector-replicate $$CNT #f))

    (let t1 (funcall @spawn @worker (to-any (the Nat 0))))
    (let t2 (funcall @spawn @worker (to-any (the Nat 1))))

    (funcall @join t1)
    (funcall @join t2)

    (return ())))
