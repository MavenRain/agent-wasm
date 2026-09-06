; Returns 1 when the proposed price is within the immutable ceiling, else 0.
; No addition is used, so this predicate cannot wrap an amount.
(export main
  (fn (run price u32)
    (if (u32-le price 100) 1 0)))
