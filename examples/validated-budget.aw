; Success packages the starting balance with the validated total.
; Nested refinements prove no overflow and compliance with the ceiling.
; Field 0 returns status: 0 success, 1 overflow, 2 above the ceiling.
; Any other field returns the accepted total, or zero on error.
(export main
  (fn (run spent u32)
    (fn (run proposed u32)
      (fn (run ceiling u32)
        (fn (run field u32)
          (let (run total u32) (add spent proposed)
            (case u32
              (if-proof
                (sum u32
                  (sigma (start u32)
                    (refine
                      (bounded
                        (refine (n u32)
                          (eq (if (u32-lt n start) 1 0) 0)))
                      (eq (if (u32-le (value bounded) ceiling) 1 0) 1))))
                (u32-lt total spent)
                (overflow
                  (inl
                    (sigma (start u32)
                      (refine
                        (bounded
                          (refine (n u32)
                            (eq (if (u32-lt n start) 1 0) 0)))
                        (eq (if (u32-le (value bounded) ceiling) 1 0) 1)))
                    1))
                (safe
                  (if-proof
                    (sum u32
                      (sigma (start u32)
                        (refine
                          (bounded
                            (refine (n u32)
                              (eq (if (u32-lt n start) 1 0) 0)))
                          (eq (if (u32-le (value bounded) ceiling) 1 0) 1))))
                    (u32-le total ceiling)
                    (within
                      (inr u32
                        (dpair
                          (sigma (start u32)
                            (refine
                              (bounded
                                (refine (n u32)
                                  (eq (if (u32-lt n start) 1 0) 0)))
                              (eq
                                (if (u32-le (value bounded) ceiling) 1 0) 1)))
                          spent
                          (pack
                            (refine
                              (bounded
                                (refine (n u32)
                                  (eq (if (u32-lt n spent) 1 0) 0)))
                              (eq
                                (if (u32-le (value bounded) ceiling) 1 0) 1))
                            (pack
                              (refine (n u32)
                                (eq (if (u32-lt n spent) 1 0) 0))
                              total safe)
                            within))))
                    (above
                      (inl
                        (sigma (start u32)
                          (refine
                            (bounded
                              (refine (n u32)
                                (eq (if (u32-lt n start) 1 0) 0)))
                            (eq
                              (if (u32-le (value bounded) ceiling) 1 0) 1)))
                        2)))))
              (error (if (u32-eq field 0) error 0))
              (accepted
                (if (u32-eq field 0) 0
                  (value (value (snd accepted))))))))))))
