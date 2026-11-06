import Mathlib

/-Let a ∈ ℝ, the equation ||x-a|-a| = 2 has exactly three distinct roots, then a = ? -/

theorem algebra_303368 (a : ℝ) (h : {x : ℝ | abs (|x - a| - a) = 2}.encard = 3) :
    a = 2 := by

    set s:= {x : ℝ | abs (|x - a| - a) = 2}
    by_contra! la
    have l: a < -2 ∨ a = -2 ∨ -2 < a ∧ a < 2 ∨ 2 < a := by
      by_cases l: a < -2
      .
        left
        exact l
      .
        by_cases r: a = -2
        .
          simp [r]
        .
          right
          right
          by_cases s: 2 < a
          .
            right
            exact s
          .
            left
            constructor
            .
              simp at l
              by_contra! o
              have u: a = -2 := by linarith
              simp [u] at r
            .
              simp at s
              by_contra! o
              have u: a = 2 := by linarith
              simp [u] at la

    rcases l with l | l | l | l

    -- case a < -2, we show s.encard = 0
    .
      have c: s.encard = 0 := by
        simp
        ext x
        simp
        intro hx
        simp [s] at hx
        apply eq_or_eq_neg_of_abs_eq at hx
        rcases hx with hx | hx
        .
          replace hx: |x - a| = a + 2 := by
            linarith
          have c: 0 ≤ a + 2 := by
            rw [← hx]
            apply abs_nonneg
          nlinarith
        .
          replace hx: |x - a| = a - 2 := by
            linarith
          have c: 0 ≤ a - 2 := by
            rw [← hx]
            apply abs_nonneg
          nlinarith
      simp [c] at h

    -- case a = -2, we show s.encard ≤ 1
    .
      have c: s.encard ≤ 1 := by
        rw [Set.encard_le_one_iff_eq]
        right
        use -2
        ext x
        constructor
        .
          intro hx
          simp [s, l] at hx
          apply eq_or_eq_neg_of_abs_eq at hx
          rcases hx with hx | hx
          .
            replace hx: |x + 2| = 0 := by
              linarith
            have hx: x + 2 = 0 := by
              rw [abs_eq_zero] at hx
              exact hx
            simp
            linarith
          .
            replace hx: |x + 2| = -4 := by
              linarith
            have c: 0 ≤ -4 := by
              rify
              rw [← hx]
              apply abs_nonneg
            nlinarith
        .
          intro hx
          simp at hx
          simp [s, hx, l]
      simp [h] at c

    -- case -2 < a ∧ a < 2, we show s.encard ≤ 2
    .
      have c: s.encard ≤ 2 := by
        have o: -2 ∈ s := by
          simp [s]
          rw [show |-2 - a| = - (-2 - a) by apply abs_of_nonpos; linarith]
          simp
        have j:= Set.encard_diff_singleton_of_mem o
        have k: (s \ {-2}).encard ≤ 1 := by
          rw [Set.encard_le_one_iff_eq]
          right
          use (2 * a + 2)
          ext x
          constructor
          .
              intro hx
              simp [s] at hx
              rcases hx with ⟨f, g⟩
              apply eq_or_eq_neg_of_abs_eq at f
              rcases f with f | f
              .
                replace f: |x - a| = a + 2 := by
                  linarith
                apply eq_or_eq_neg_of_abs_eq at f
                rcases f with f | f
                .
                  simp
                  linarith
                .
                  absurd g
                  linarith
              .
                replace f: |x - a| = a - 2 := by
                  linarith
                have c: 0 ≤ a - 2 := by
                  rw [← f]
                  apply abs_nonneg
                nlinarith

          .
              intro hx
              simp at hx
              simp [hx, s]
              constructor
              .
                rw [show 2 * a + 2 - a = a + 2 by
                  linarith]
                rw [show |a + 2| = a + 2 by
                  apply abs_of_nonneg
                  linarith]
                simp
              .
                by_contra! p
                replace p: a = -2 := by linarith
                simp [p] at l
        rw [j] at k
        clear * - k
        set t:= s.encard
        simp at k
        norm_num at k
        exact k

      simp [h] at c
      norm_num at c

    -- case 2 < a, we show s.encard = 4
    .
      let t: Set ℝ := {(-2: ℝ), (2: ℝ), 2 * a + 2, 2 * a - 2}
      have c: s.encard = 4 := by
        have f1: 2 ∈ s := by
          simp [s]
          rw [show |2 - a| = - (2 - a) by apply abs_of_nonpos; linarith]
          simp
        have g1:= Set.encard_diff_singleton_of_mem f1
        have c1: (s \ {2}).encard = 3 := by
          rw [h] at g1
          clear h
          have f2: -2 ∈ s \ {2} := by
            simp [s]
            constructor
            .
              rw [show |-2 - a| = - (-2 - a) by apply abs_of_nonpos; linarith]
              simp
            .
              norm_num
          have g2:= Set.encard_diff_singleton_of_mem f2
          have c2: ((s \ {2}) \ {-2}).encard = 2 := by
            rw [Set.encard_eq_two]
            use (2 * a + 2)
            use (2 * a - 2)
            constructor
            .
              linarith
            .
              ext x
              constructor
              .
                intro hx
                simp [s] at hx
                rcases hx with ⟨i, j⟩
                rcases i with ⟨i, k⟩
                apply eq_or_eq_neg_of_abs_eq at i
                rcases i with i | i
                .
                  replace i: |x - a| = a + 2 := by
                    linarith
                  apply eq_or_eq_neg_of_abs_eq at i
                  rcases i with i | i
                  .
                    simp
                    left
                    linarith
                  .
                    simp
                    right
                    absurd j
                    linarith
                .
                  replace i: |x - a| = a - 2 := by
                    linarith
                  apply eq_or_eq_neg_of_abs_eq at i
                  rcases i with i | i
                  .
                    simp
                    right
                    linarith
                  .
                    simp
                    left
                    absurd k
                    linarith
              .
                intro hx
                simp at hx
                rcases hx with i | i
                .
                  simp [i, s]
                  constructor
                  .
                    constructor
                    .
                      rw [show 2 * a + 2 - a = a + 2 by
                        linarith]
                      rw [show |a + 2| = a + 2 by
                        apply abs_of_nonneg
                        linarith]
                      simp
                    .
                      linarith
                  .
                    linarith
                .
                  simp [i, s]
                  constructor
                  .
                    constructor
                    .
                      rw [show 2 * a - 2 - a = a - 2 by
                        linarith]
                      rw [show |a - 2| = a - 2 by
                        apply abs_of_nonneg
                        linarith]
                      simp
                    .
                      linarith
                  .
                    linarith

          rw [c2] at g2
          set t:= (s \ {2}).encard
          clear * - g2 g1
          simp [g1] at g2
          norm_cast at g2

        rw [h,c1] at g1
        norm_cast at g1

      simp [c] at h