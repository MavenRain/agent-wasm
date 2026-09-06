; The expected proof type depends on both n and value.
; n and evidence vanish, while value is a real runtime argument.
(export main
  (fn (run input u32)
    (app erase
      (app run
        (app erase
          (fn (erase n u32)
            (fn (run value u32)
              (fn (erase evidence (eq value n)) (add value 1))))
          input)
        input)
      (refl input))))
