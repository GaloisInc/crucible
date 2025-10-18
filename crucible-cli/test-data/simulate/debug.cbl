(defun @main () Unit
  (start start:
    (print "before!\n")
    ; Slightly awkward, `@debug-run` prepends the statement to the debugger
    ; input, so these are actually run in the reverse order ("bt" then "quit").
    (funcall @debug-run "quit")
    (funcall @debug-run "bt")
    (funcall @debug)
    (print "after!\n")
    (return ())))
