import Mathlib

/-All real numbers c that make the equation
∣x−1∣−∣x−2∣+2∣x−3∣= c
have exactly two solutions are -/

theorem algebra_319129: {c: ℝ | {x : ℝ | abs (x - 1) - abs (x - 2) + 2 * abs (x - 3) = c}.encard = 2}
    = Set.Ioi 1 \ {3} := by

    ext c
    constructor
    -- the forward direction
    .
      intro h
      simp at h
      set s:= {x : ℝ | abs (x - 1) - abs (x - 2) + 2 * abs (x - 3) = c}
      by_contra! o
      simp at o
      by_cases l: c ≤ 1

      -- case c ≤ 1
      .
        by_cases r: c < 1
        -- case c < 1
        .
          -- we show that s is empty
          have contra: s.encard = 0 := by
            simp
            ext x
            simp
            intro hx
            simp [s] at hx
            by_cases lx: x ≤ 1
            -- case x ≤ 1
            .
              rw [show |x - 1| = - (x - 1) by apply abs_of_nonpos; linarith] at hx
              rw [show |x - 2| = - (x - 2) by apply abs_of_nonpos; linarith] at hx
              rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith] at hx
              nlinarith
            -- case x > 1
            rw [show |x - 1| = x - 1 by apply abs_of_pos; linarith] at hx
            by_cases lx2: x ≤ 2
            -- case x ≤ 2
            .
              rw [show |x - 2| = - (x - 2) by apply abs_of_nonpos; linarith] at hx
              rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith] at hx
              nlinarith
            -- case x > 2
            .
              rw [show |x - 2| = x - 2 by apply abs_of_pos; linarith] at hx
              by_cases lx3: x ≤ 3
              -- case x ≤ 3
              .
                rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith] at hx
                nlinarith
              -- case x > 3
              .
                rw [show |x - 3| = x - 3 by apply abs_of_pos; linarith] at hx
                nlinarith

          simp [contra] at h

        -- case c = 1
        .
          -- we show s = {3}
          simp at r
          have oc: c = 1 := by linarith
          have contra: s.encard = 1 := by
            have t: s = {3} := by
              simp [s]
              ext x
              constructor
              .
                intro hx
                simp [s] at hx
                by_cases lx: x ≤ 1
                -- case x ≤ 1
                .
                  rw [show |x - 1| = - (x - 1) by apply abs_of_nonpos; linarith] at hx
                  rw [show |x - 2| = - (x - 2) by apply abs_of_nonpos; linarith] at hx
                  rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith] at hx
                  nlinarith
                -- case x > 1
                rw [show |x - 1| = x - 1 by apply abs_of_pos; linarith] at hx
                by_cases lx2: x ≤ 2
                -- case x ≤ 2
                .
                  rw [show |x - 2| = - (x - 2) by apply abs_of_nonpos; linarith] at hx
                  rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith] at hx
                  nlinarith
                -- case x > 2
                .
                  rw [show |x - 2| = x - 2 by apply abs_of_pos; linarith] at hx
                  by_cases lx3: x ≤ 3
                  -- case x ≤ 3
                  .
                    rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith] at hx
                    simp
                    nlinarith
                  -- case x > 3
                  .
                    rw [show |x - 3| = x - 3 by apply abs_of_pos; linarith] at hx
                    nlinarith
              .
                intro hx
                simp at hx
                simp [hx, oc]
                norm_num

            rw [t]
            simp
          simp [contra] at h

      -- case c > 1
      .
        -- we show that 3 ≤ s.encard
        simp at l
        simp [l] at o
        have t: {1, 2, 4} ⊆ s:= by
          simp [s]
          intro x hx
          simp at hx
          rcases hx with hx | hx | hx
          .
            simp [hx, o]
            norm_num
          .
            simp [hx, o]
            norm_num
          .
            simp [hx, o]
            norm_num
        have o: {1, 2, 4} = s := by
          apply Set.Finite.eq_of_subset_of_encard_le' at t
          rw [h] at t
          simp [Set.encard] at t
          norm_num at t
          exact t
          simp
        rw [← o] at h
        simp [Set.encard] at h


    -- the backward direction
    .
      intro h
      simp at h
      rcases h with ⟨l, ne⟩
      simp
      set s:= {x : ℝ | abs (x - 1) - abs (x - 2) + 2 * abs (x - 3) = c}
      by_cases r: c < 3
      .
        -- case c < 3
        clear ne
        -- we show that the solutions are exactly (c + 5) / 2 and (7 - c) / 2
        have hs: s = {(c + 5) / 2, (7 - c) / 2} := by
          ext x
          simp [s]
          constructor
          .
            intro h
            by_cases l: x ≤ 1
            -- case x ≤ 1
            .
              rw [show |x - 1| = - (x - 1) by apply abs_of_nonpos; linarith] at h
              rw [show |x - 2| = - (x - 2) by apply abs_of_nonpos; linarith] at h
              rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith] at h
              nlinarith
            -- case x > 1
            rw [show |x - 1| = x - 1 by apply abs_of_pos; linarith] at h
            by_cases l2: x ≤ 2
            -- case x ≤ 2
            .
              rw [show |x - 2| = - (x - 2) by apply abs_of_nonpos; linarith] at h
              rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith] at h
              nlinarith
            -- case x > 2
            .
              rw [show |x - 2| = x - 2 by apply abs_of_pos; linarith] at h
              by_cases l3: x ≤ 3
              -- case x ≤ 3
              .
                rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith] at h
                right
                nlinarith
              -- case x > 3
              .
                rw [show |x - 3| = x - 3 by apply abs_of_pos; linarith] at h
                left
                nlinarith
          .
            intro h
            rcases h with h | h
            .
              have lx1: 3 < x := by linarith
              have lx2: x < 4 := by linarith
              rw [show |x - 1| = x - 1 by apply abs_of_pos; linarith]
              rw [show |x - 2| = x - 2 by apply abs_of_pos; linarith]
              rw [show |x - 3| = x - 3 by apply abs_of_pos; linarith]
              nlinarith
            .
              have lx1: 2 < x := by linarith
              have lx2: x < 3 := by linarith
              rw [show |x - 1| = x - 1 by apply abs_of_pos; linarith]
              rw [show |x - 2| = x - 2 by apply abs_of_pos; linarith]
              rw [show |x - 3| = - (x - 3) by apply abs_of_neg; linarith]
              nlinarith

        rw [hs]
        rw [Set.encard_eq_two]
        use (c + 5) / 2
        use (7 - c) / 2
        constructor
        .
          nlinarith
        .
          rfl
      -- case 3 < c
      .
        replace l: 3 < c := by
          by_contra! o
          simp at r
          have v: c = 3 := by linarith
          simp [v] at ne
        clear ne r
        -- we show that the solutions are exactly (c + 5) / 2 and (5 - c) / 2
        have hs: s = {(c + 5) / 2, (5 - c) / 2} := by
          ext x
          simp [s]
          constructor
          .
            intro h
            by_cases l: x ≤ 1
            -- case x ≤ 1
            .
              rw [show |x - 1| = - (x - 1) by apply abs_of_nonpos; linarith] at h
              rw [show |x - 2| = - (x - 2) by apply abs_of_nonpos; linarith] at h
              rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith] at h
              right
              nlinarith
            -- case x > 1
            rw [show |x - 1| = x - 1 by apply abs_of_pos; linarith] at h
            by_cases l2: x ≤ 2
            -- case x ≤ 2
            .
              rw [show |x - 2| = - (x - 2) by apply abs_of_nonpos; linarith] at h
              rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith] at h
              nlinarith
            -- case x > 2
            .
              rw [show |x - 2| = x - 2 by apply abs_of_pos; linarith] at h
              by_cases l3: x ≤ 3
              -- case x ≤ 3
              .
                rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith] at h
                right
                nlinarith
              -- case x > 3
              .
                rw [show |x - 3| = x - 3 by apply abs_of_pos; linarith] at h
                left
                nlinarith
          .
            intro h
            rcases h with h | h
            .
              have lx: 4 < x := by linarith
              rw [show |x - 1| = x - 1 by apply abs_of_pos; linarith]
              rw [show |x - 2| = x - 2 by apply abs_of_pos; linarith]
              rw [show |x - 3| = x - 3 by apply abs_of_pos; linarith]
              nlinarith
            .
              have lx: x < 2 := by linarith
              by_cases l4: x ≤ 1
              -- case x ≤ 1
              .
                rw [show |x - 1| = - (x - 1) by apply abs_of_nonpos; linarith]
                rw [show |x - 2| = - (x - 2) by apply abs_of_nonpos; linarith]
                rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith]
                nlinarith
              -- case x > 1
              .
                rw [show |x - 1| = x - 1 by apply abs_of_pos; linarith]
                rw [show |x - 2| = - (x - 2) by apply abs_of_nonpos; linarith]
                rw [show |x - 3| = - (x - 3) by apply abs_of_nonpos; linarith]
                nlinarith
        rw [hs]
        rw [Set.encard_eq_two]
        use (c + 5) / 2
        use (5 - c) / 2
        constructor
        .
          nlinarith
        .
          rfl
