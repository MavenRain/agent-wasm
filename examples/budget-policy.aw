(export main
  (fn (run spent u32)
    (fn (run proposed u32)
      (fn (run ceiling u32)
        (let (run total u32) (add spent proposed)
          (let (run allowed bool)
            (if (u32-lt total spent) false (u32-le total ceiling))
            (if allowed 1 0)))))))
