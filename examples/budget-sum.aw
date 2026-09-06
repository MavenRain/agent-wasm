; Left is an error code, right is the accepted total.
; The final case adapts the internal sum to the scalar export ABI.
(export main
  (fn (run spent u32)
    (fn (run proposed u32)
      (fn (run ceiling u32)
        (fn (run field u32)
          (let (run total u32) (add spent proposed)
            (let (run result (sum u32 u32))
              (if (u32-lt total spent)
                (inl u32 1)
                (if (u32-le total ceiling)
                  (inr u32 total)
                  (inl u32 2)))
              (case u32 result
                (error (if (u32-eq field 0) error 0))
                (value (if (u32-eq field 0) 0 value))))))))))
