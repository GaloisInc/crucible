(declare @strcmp ((s1 (Ptr 64)) (s2 (Ptr 64))) (Bitvector 32))
(declare @write-c-string ((dst Pointer) (src (String Unicode))) Unit)

(defun @main () Unit
  (start start:
    (let hello1 (alloca none (bv 64 6)))
    (let hello2 (alloca none (bv 64 6)))
    (funcall @write-c-string hello1 "Hello")
    (funcall @write-c-string hello2 "Hello")

    (let abc (alloca none (bv 64 4)))
    (funcall @write-c-string abc "abc")

    (let xyz (alloca none (bv 64 4)))
    (funcall @write-c-string xyz "xyz")

    (let empty1 (alloca none (bv 64 1)))
    (let empty2 (alloca none (bv 64 1)))
    (funcall @write-c-string empty1 "")
    (funcall @write-c-string empty2 "")

    (let ab (alloca none (bv 64 3)))
    (funcall @write-c-string ab "ab")

    ;; strcmp of equal strings
    (let r1 (funcall @strcmp hello1 hello2))
    (assert! (equal? r1 (bv 32 0)) "strcmp('Hello', 'Hello') == 0")

    ;; strcmp of different strings - first is less
    (let r2 (funcall @strcmp abc xyz))
    (assert! (<$ r2 (bv 32 0)) "strcmp('abc', 'xyz') < 0")

    ;; strcmp of different strings - first is greater
    (let r3 (funcall @strcmp xyz abc))
    (assert! (<$ (bv 32 0) r3) "strcmp('xyz', 'abc') > 0")

    ;; strcmp with aliased strings (same pointer)
    (let r5 (funcall @strcmp hello1 hello1))
    (assert! (equal? r5 (bv 32 0)) "strcmp(s, s) == 0")

    ;; strcmp with empty strings
    (let r6 (funcall @strcmp empty1 empty2))
    (assert! (equal? r6 (bv 32 0)) "strcmp('', '') == 0")

    ;; strcmp where first string is a prefix
    (let r7 (funcall @strcmp ab abc))
    (assert! (<$ r7 (bv 32 0)) "strcmp('ab', 'abc') < 0")

    ;; strcmp where second string is a prefix
    (let r8 (funcall @strcmp abc ab))
    (assert! (<$ (bv 32 0) r8) "strcmp('abc', 'ab') > 0")

    (return ())))
