# 0.6

## Bug fixes

* `Any`-typed local variables are no longer initialized to a default value,
  which prevents spurious assertion failures if these variables become involved
  in symbolic branches in certain cases.
