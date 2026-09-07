; The immutable allowlist contains tool IDs 7 and 9. Error precedence is:
; 1 disallowed tool, 2 wrapping addition, 3 total above ceiling.
; Field 0 returns status; every other field returns accepted total or zero.
; Success pairs an action record with a total proven equal to that action's
; wrapped spent + proposed, at least spent (no wrap), and at most ceiling.
; Its final refinement proves the paired action's tool belongs to {7,9}.
; The scalar adapter consumes this checked package; it grants no host authority.
(export main
  (fn (run tool u32)
    (fn (run spent u32)
      (fn (run proposed u32)
        (fn (run ceiling u32)
          (fn (run field u32)
            (let (run request (record (tool u32) (spent u32) (proposed u32)))
              (record (tool tool) (spent spent) (proposed proposed))
              (let
                (run total
                  (refine (n u32)
                    (eq n
                      (add (field request spent) (field request proposed)))))
                (pack
                  (refine (n u32)
                    (eq n (add (field request spent) (field request proposed))))
                  (add (field request spent) (field request proposed))
                  (refl (add (field request spent) (field request proposed))))
                (case u32
                  (if-proof
                    (sum u32
                      (sigma
                        (action (record (tool u32) (spent u32) (proposed u32)))
                        (refine
                          (validated
                            (refine
                              (bounded
                                (refine
                                  (sum
                                    (refine (n u32)
                                      (eq n
                                        (add (field action spent)
                                          (field action proposed)))))
                                  (eq
                                    (if
                                      (u32-lt (value sum) (field action spent))
                                      1
                                      0)
                                    0)))
                              (eq
                                (if (u32-le (value (value bounded)) ceiling)
                                  1
                                  0)
                                1)))
                          (eq
                            (if
                              (if
                                (u32-eq (field action tool) 7)
                                true
                                (u32-eq (field action tool) 9))
                              1
                              0)
                            1))))
                    (if (u32-eq (field request tool) 7)
                      true
                      (u32-eq (field request tool) 9))
                    (permitted
                      (if-proof
                        (sum u32
                          (sigma
                            (action
                              (record (tool u32) (spent u32) (proposed u32)))
                            (refine
                              (validated
                                (refine
                                  (bounded
                                    (refine
                                      (sum
                                        (refine (n u32)
                                          (eq n
                                            (add (field action spent)
                                              (field action proposed)))))
                                      (eq
                                        (if
                                          (u32-lt (value sum)
                                            (field action spent))
                                          1
                                          0)
                                        0)))
                                  (eq
                                    (if (u32-le (value (value bounded)) ceiling)
                                      1
                                      0)
                                    1)))
                              (eq
                                (if
                                  (if
                                    (u32-eq (field action tool) 7)
                                    true
                                    (u32-eq (field action tool) 9))
                                  1
                                  0)
                                1))))
                        (u32-lt (value total) (field request spent))
                        (overflow
                          (inl
                            (sigma
                              (action
                                (record (tool u32) (spent u32) (proposed u32)))
                              (refine
                                (validated
                                  (refine
                                    (bounded
                                      (refine
                                        (sum
                                          (refine (n u32)
                                            (eq n
                                              (add
                                                (field action spent)
                                                (field action proposed)))))
                                        (eq
                                          (if
                                            (u32-lt (value sum)
                                              (field action spent))
                                            1
                                            0)
                                          0)))
                                    (eq
                                      (if
                                        (u32-le (value (value bounded)) ceiling)
                                        1
                                        0)
                                      1)))
                                (eq
                                  (if
                                    (if
                                      (u32-eq (field action tool) 7)
                                      true
                                      (u32-eq (field action tool) 9))
                                    1
                                    0)
                                  1)))
                            2))
                        (safe
                          (if-proof
                            (sum u32
                              (sigma
                                (action
                                  (record (tool u32)
                                    (spent u32)
                                    (proposed u32)))
                                (refine
                                  (validated
                                    (refine
                                      (bounded
                                        (refine
                                          (sum
                                            (refine (n u32)
                                              (eq n
                                                (add
                                                  (field action spent)
                                                  (field action proposed)))))
                                          (eq
                                            (if
                                              (u32-lt (value sum)
                                                (field action spent))
                                              1
                                              0)
                                            0)))
                                      (eq
                                        (if
                                          (u32-le (value (value bounded))
                                            ceiling)
                                          1
                                          0)
                                        1)))
                                  (eq
                                    (if
                                      (if
                                        (u32-eq (field action tool) 7)
                                        true
                                        (u32-eq (field action tool) 9))
                                      1
                                      0)
                                    1))))
                            (u32-le (value total) ceiling)
                            (within
                              (inr u32
                                (dpair
                                  (sigma
                                    (action
                                      (record (tool u32)
                                        (spent u32)
                                        (proposed u32)))
                                    (refine
                                      (validated
                                        (refine
                                          (bounded
                                            (refine
                                              (sum
                                                (refine (n u32)
                                                  (eq n
                                                    (add
                                                      (field action spent)
                                                      (field action
                                                        proposed)))))
                                              (eq
                                                (if
                                                  (u32-lt (value sum)
                                                    (field action spent))
                                                  1
                                                  0)
                                                0)))
                                          (eq
                                            (if
                                              (u32-le (value (value bounded))
                                                ceiling)
                                              1
                                              0)
                                            1)))
                                      (eq
                                        (if
                                          (if
                                            (u32-eq (field action tool) 7)
                                            true
                                            (u32-eq (field action tool) 9))
                                          1
                                          0)
                                        1)))
                                  request
                                  (pack
                                    (refine
                                      (validated
                                        (refine
                                          (bounded
                                            (refine
                                              (sum
                                                (refine (n u32)
                                                  (eq n
                                                    (add
                                                      (field request spent)
                                                      (field request
                                                        proposed)))))
                                              (eq
                                                (if
                                                  (u32-lt (value sum)
                                                    (field request spent))
                                                  1
                                                  0)
                                                0)))
                                          (eq
                                            (if
                                              (u32-le (value (value bounded))
                                                ceiling)
                                              1
                                              0)
                                            1)))
                                      (eq
                                        (if
                                          (if
                                            (u32-eq (field request tool) 7)
                                            true
                                            (u32-eq (field request tool) 9))
                                          1
                                          0)
                                        1))
                                    (pack
                                      (refine
                                        (bounded
                                          (refine
                                            (sum
                                              (refine (n u32)
                                                (eq n
                                                  (add
                                                    (field request spent)
                                                    (field request proposed)))))
                                            (eq
                                              (if
                                                (u32-lt (value sum)
                                                  (field request spent))
                                                1
                                                0)
                                              0)))
                                        (eq
                                          (if
                                            (u32-le (value (value bounded))
                                              ceiling)
                                            1
                                            0)
                                          1))
                                      (pack
                                        (refine
                                          (sum
                                            (refine (n u32)
                                              (eq n
                                                (add
                                                  (field request spent)
                                                  (field request proposed)))))
                                          (eq
                                            (if
                                              (u32-lt (value sum)
                                                (field request spent))
                                              1
                                              0)
                                            0))
                                        total
                                        safe)
                                      within)
                                    permitted))))
                            (above
                              (inl
                                (sigma
                                  (action
                                    (record (tool u32)
                                      (spent u32)
                                      (proposed u32)))
                                  (refine
                                    (validated
                                      (refine
                                        (bounded
                                          (refine
                                            (sum
                                              (refine (n u32)
                                                (eq n
                                                  (add
                                                    (field action spent)
                                                    (field action proposed)))))
                                            (eq
                                              (if
                                                (u32-lt (value sum)
                                                  (field action spent))
                                                1
                                                0)
                                              0)))
                                        (eq
                                          (if
                                            (u32-le (value (value bounded))
                                              ceiling)
                                            1
                                            0)
                                          1)))
                                    (eq
                                      (if
                                        (if
                                          (u32-eq (field action tool) 7)
                                          true
                                          (u32-eq (field action tool) 9))
                                        1
                                        0)
                                      1)))
                                3))))))
                    (denied
                      (inl
                        (sigma
                          (action
                            (record (tool u32) (spent u32) (proposed u32)))
                          (refine
                            (validated
                              (refine
                                (bounded
                                  (refine
                                    (sum
                                      (refine (n u32)
                                        (eq n
                                          (add (field action spent)
                                            (field action proposed)))))
                                    (eq
                                      (if
                                        (u32-lt (value sum)
                                          (field action spent))
                                        1
                                        0)
                                      0)))
                                (eq
                                  (if (u32-le (value (value bounded)) ceiling)
                                    1
                                    0)
                                  1)))
                            (eq
                              (if
                                (if
                                  (u32-eq (field action tool) 7)
                                  true
                                  (u32-eq (field action tool) 9))
                                1
                                0)
                              1)))
                        1)))
                  (error (if (u32-eq field 0) error 0))
                  (accepted
                    (if (u32-eq field 0)
                      0
                      (value (value (value (value (snd accepted))))))))))))))))
