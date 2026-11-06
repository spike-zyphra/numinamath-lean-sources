import Mathlib

/-The equation ||x| - 1| = a has exactly three real solutions. Then a equals-/

theorem algebra_307317 {a: ℝ}
  (h: {x: ℝ | abs (|x| - 1) = a}.encard = 3): a = 1 := by

  by_contra! n
  set s:= {x: ℝ | abs (|x| - 1) = a}
  by_cases l: a < 0
  -- case a < 0, we show s.encard = 0
  .
    have o: s = ∅ := by
      ext x
      simp
      intro r
      simp [s] at r
      have j: 0 ≤ a := by
        rw [← r]
        apply abs_nonneg
      linarith
    simp [o] at h
  .
    by_cases i: a = 0
    -- case a = 0, we show s.encard = 2
    .
      have o: s.encard = 2 := by
        rw [Set.encard_eq_two]
        use 1
        use -1
        norm_num
        simp [s, i]
        ext x
        constructor
        .
          intro h
          simp at h
          by_cases lx: 0 ≤ x
          .
            rw [show |x| = x by apply abs_of_nonneg; linarith] at h
            simp
            left
            linarith
          .
            rw [show |x| = -x by apply abs_of_neg; linarith] at h
            simp
            right
            linarith
        .
          intro h
          simp at h
          rcases h with h | h
          .
            simp [h]
          .
            simp [h]

      simp [o] at h

    .
      by_cases j: a < 1
      -- case 0 < a < 1, we show s.encard = 4
      .
        simp at l
        replace l: 0 < a := by
          by_contra! k
          have g: a = 0 := by
            linarith
          simp [g] at i
        clear i
        have o: s.encard = 4 := by
          have h_eq: s = {1 + a, -1 - a, 1 - a, -1 + a} := by
            ext x
            simp [s]
            constructor
            -- the forward direction
            .
              intro h
              simp at h
              by_cases lx: 0 ≤ x
              .
                rw [show |x| = x by apply abs_of_nonneg; linarith] at h
                by_cases l2: x ≤ 1
                .
                  rw [show |x - 1| = - (x - 1) by apply abs_of_nonpos; linarith] at h
                  right
                  right
                  left
                  linarith
                .
                  rw [show |x - 1| = x - 1 by apply abs_of_pos; linarith] at h
                  left
                  linarith

              .
                simp at lx
                rw [show |x| = - x by apply abs_of_nonpos; linarith] at h
                by_cases l2: x ≤ -1
                .
                  rw [show |-x - 1| = -x - 1 by apply abs_of_nonneg; linarith] at h
                  right
                  left
                  linarith
                .
                  rw [show |-x - 1| = - (-x - 1) by apply abs_of_nonpos; linarith] at h
                  right
                  right
                  right
                  linarith
            -- the backward direction
            .
              intro h
              rcases h with h | h | h | h
              .
                simp [h]
                rw [show |1 + a| = 1 + a by apply abs_of_nonneg; linarith]
                simp
                linarith
              .
                simp [h]
                rw [show |-1 - a| = - (-1 - a) by apply abs_of_neg; linarith]
                simp
                linarith
              .
                simp [h]
                rw [show |1 - a| = 1 - a by apply abs_of_nonneg; linarith]
                simp
                linarith
              .
                simp [h]
                rw [show |-1 + a| = - (-1 + a) by apply abs_of_neg; linarith]
                simp
                linarith

          rw [h_eq]
          repeat rw [Set.encard_insert_of_not_mem]
          norm_num
          simp
          linarith
          simp
          norm_num
          linarith
          simp
          norm_num
          constructor
          .
            linarith
          .
            linarith

        simp [o] at h

      -- 1 < a, we show s.encard = 2
      .
        simp at j
        have k: 1 < a := by
          by_contra! o
          have g: a = 1 := by
            linarith
          simp [g] at n
        clear l i j
        have o: s.encard = 2 := by
          have h_eq: s = {1 + a, -a - 1} := by
            ext x
            simp [s]
            constructor
            -- the forward direction
            .
              intro h
              simp at h
              by_cases lx: 0 ≤ x
              .
                rw [show |x| = x by apply abs_of_nonneg; linarith] at h
                by_cases l2: x ≤ 1
                .
                  rw [show |x - 1| = - (x - 1) by apply abs_of_nonpos; linarith] at h
                  nlinarith
                .
                  rw [show |x - 1| = x - 1 by apply abs_of_pos; linarith] at h
                  left
                  linarith

              .
                simp at lx
                rw [show |x| = - x by apply abs_of_nonpos; linarith] at h
                by_cases l2: x ≤ -1
                .
                  rw [show |-x - 1| = -x - 1 by apply abs_of_nonneg; linarith] at h
                  right
                  linarith
                .
                  rw [show |-x - 1| = - (-x - 1) by apply abs_of_nonpos; linarith] at h
                  nlinarith
            -- the backward direction
            .
              intro h
              rcases h with h | h
              .
                simp [h]
                rw [show |1 + a| = 1 + a by apply abs_of_nonneg; linarith]
                simp
                linarith
              .
                simp [h]
                rw [show |-a - 1| = - (-a - 1) by apply abs_of_neg; linarith]
                simp
                linarith

          simp [h_eq]
          repeat rw [Set.encard_insert_of_not_mem]
          .
            norm_num
          .
            simp
            linarith

        simp [o] at h
        
