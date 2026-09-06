; A runtime payload carries checked equality evidence that disappears in erasure.
(export main
  (fn (run n u32)
    (let (erase same (eq (add n 1) (add n 1))) (refl (add n 1))
      (let (run result (refine (item u32) (eq item (add n 1))))
        (pack (refine (item u32) (eq item (add n 1))) (add n 1) same)
        (let (erase checked (eq (value result) (add n 1))) (evidence result)
          (value result))))))
