; Immutable tool identifiers 7 and 9 are allowed, with a price ceiling of 100.
; This returns a decision only. It does not grant host authority or return proof.
(export main
  (fn (run tool u32)
    (fn (run price u32)
      (app run
        (fn (run action (product u32 u32))
          (if (u32-le (snd action) 100)
            (if (u32-eq (fst action) 7) 1
              (if (u32-eq (fst action) 9) 1 0))
            0))
        (pair tool price)))))
