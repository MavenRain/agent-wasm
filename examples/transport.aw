; Symmetry follows by transporting refl a along an abstract equality a = b.
; The helper and all its applications are ghost computations.
(export main
  (let (erase symmetry
    (pi (erase a u32)
      (pi (erase b u32)
        (pi (erase proof (eq a b)) (eq b a)))))
    (fn (erase a u32)
      (fn (erase b u32)
        (fn (erase proof (eq a b))
          (transport (index (eq index a)) a b proof (refl a)))))
    (fn (run input u32)
      (let (erase reversed (eq input input))
        (app erase (app erase (app erase symmetry input) input) (refl input))
        (add input 1)))))
