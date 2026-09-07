; A successful result carries erased evidence that its value meets the ceiling.
(export main
  (fn (run amount u32)
    (fn (run ceiling u32)
      (case u32
        (if-proof
          (sum u32 (refine (n u32) (eq (if (u32-le n ceiling) 1 0) 1)))
          (u32-le amount ceiling)
          (yes
            (inr u32
              (pack (refine (n u32) (eq (if (u32-le n ceiling) 1 0) 1))
                amount yes)))
          (no
            (inl (refine (n u32) (eq (if (u32-le n ceiling) 1 0) 1)) 0)))
        (error error)
        (accepted (value accepted))))))
