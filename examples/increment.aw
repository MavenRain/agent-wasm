; Equality evidence is checked and erased before the runtime IR exists.
(export main
  (fn (run x u32)
    (let (erase same (eq x x)) (refl x)
      (add x 1))))
