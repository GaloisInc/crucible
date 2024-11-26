; A regression test for #1024.

(defun @exotic-fresh-names () Bool
  (start start:
    ; Although the list of allowable characters in What4 solver names is very
    ; small, we can nevertheless define atom names with unallowable characters
    ; by Z-encoding them under the hood.
    (let ω (fresh Bool))                ; Fancy Unicode characters
    (let hyphens-are-fine (fresh Bool)) ; Hyphens
    (return (and ω hyphens-are-fine))))
