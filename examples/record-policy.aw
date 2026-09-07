; Immutable tool identifiers 7 and 9 are allowed, with a price ceiling of 100.
; Success carries the named action and erased evidence of the entire policy.
; The scalar adapter returns accepted price plus one, or zero for rejection.
(export main
  (fn (run tool u32)
    (fn (run price u32)
      (let (run action (record (tool u32) (price u32)))
        (record (tool tool) (price price))
        (case u32
          (if-proof
            (sum u32
              (refine (a (record (tool u32) (price u32)))
                (eq (if
                  (if (u32-le (field a price) 100)
                    (if (u32-eq (field a tool) 7) true
                      (u32-eq (field a tool) 9)) false)
                  1 0) 1)))
            (if (u32-le (field action price) 100)
              (if (u32-eq (field action tool) 7) true
                (u32-eq (field action tool) 9)) false)
            (yes
              (inr u32
                (pack
                  (refine (a (record (tool u32) (price u32)))
                    (eq (if
                      (if (u32-le (field a price) 100)
                        (if (u32-eq (field a tool) 7) true
                          (u32-eq (field a tool) 9)) false)
                      1 0) 1))
                  action yes)))
            (no
              (inl
                (refine (a (record (tool u32) (price u32)))
                  (eq (if
                    (if (u32-le (field a price) 100)
                      (if (u32-eq (field a tool) 7) true
                        (u32-eq (field a tool) 9)) false)
                    1 0) 1))
                0)))
          (error error)
          (accepted (add (field (value accepted) price) 1)))))))
