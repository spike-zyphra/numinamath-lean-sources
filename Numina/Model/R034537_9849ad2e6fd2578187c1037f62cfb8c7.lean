import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_193596 (a : ℝ) :
  ∃ x, logb 2 (x - 1) < 1 ∧ |x - a| < 2 ↔ a ∈ Ioo (-1) 5 := by
  by_cases h1 : a ≤ 1
  · -- case a ≤ 1
    use (a + 3) / 2
    constructor
    · -- Assume h
      intro h
      rcases h with ⟨h11, h12⟩
      constructor
      · -- a > -1
        have ha6 : a > -1 := by
          have h2 : |( (a + 3) / 2 ) - a| < 2 := h12
          rw [abs_lt] at h2
          linarith
        linarith
      · -- a < 5
        have ha7 : a < 5 := by
          have h111 : logb 2 (( (a + 3) / 2 - 1 ) ) < 1 := h11
          by_contra h
          push_neg at h
          have h23 : a ≥ 5 := by linarith
          have h24 : ( (a + 3) / 2 - 1 ) ≥ (2 : ℝ) := by
            nlinarith
          have h25 : logb 2 (( (a + 3) / 2 - 1 ) ) ≥ (1 : ℝ) := by
            have h32 : ( (a + 3) / 2 - 1 ) ≥ (2 : ℝ) := h24
            have h34 : logb 2 (( (a + 3) / 2 - 1 ) ) ≥ logb 2 (2 : ℝ) := by
              apply Real.logb_le_logb_of_le
              all_goals
                linarith
            have h35 : logb 2 (2 : ℝ) = 1 := by
              rw [logb_self_eq_one]
              all_goals
                linarith
            linarith
          linarith
        linarith
    · -- Assume a ∈ (-1, 5)
      rintro ⟨ha1, ha2⟩
      constructor
      · -- $\log_2(x-1) < 1$
        have h1 : logb 2 (( (a + 3) / 2 - 1 ) ) < 1 := by
          have h3 : ( (a + 3) / 2 - 1 ) > 0 := by
            nlinarith
          have h4 : ( (a + 3) / 2 - 1 ) < (2 : ℝ) := by
            nlinarith
          have h2 : logb 2 (( (a + 3) / 2 - 1 ) ) < 1 := by
            have h10 : ( (a + 3) / 2 - 1 ) < (2 : ℝ) := h4
            have h11 : logb 2 (( (a + 3) / 2 - 1 ) ) < logb 2 (2 : ℝ) := by
              apply Real.logb_lt_logb
              all_goals
                nlinarith
            have h13 : logb 2 (2 : ℝ) = 1 := by
              norm_num [logb_self_eq_one]
            linarith
          linarith
        simpa using h1
      · -- $|x - a| < 2$
        have h2 : |( (a + 3) / 2 ) - a| < 2 := by
          rw [abs_lt]
          constructor
          · -- -2 < ( (a + 3) / 2 ) - a
            nlinarith
          · -- ( (a + 3) / 2 ) - a < 2
            nlinarith
        simpa using h2
  · -- case a > 1
    use (a + 1) / 2
    constructor
    · -- Assume h
      intro h
      rcases h with ⟨h11, h12⟩
      constructor
      · -- a > -1
        have h3 : a > -1 := by
          have h4 : logb 2 (( (a + 1) / 2 - 1 ) ) < 1 := h11
          have h14 : ( (a + 1) / 2 - 1 ) > 0 := by
            by_contra h
            push_neg at h
            have h11 : logb 2 (( (a + 1) / 2 - 1 ) ) ≤ (0 : ℝ) := by
              have h7 : ( (a + 1) / 2 - 1 ) ≤ (0 : ℝ) := by
                nlinarith
              have h12 : ( (a + 1) / 2 - 1 ) ≤ (0 : ℝ) := h7
              have h13 : logb 2 (( (a + 1) / 2 - 1 ) ) = (0 : ℝ) := by
                rw [Real.logb_eq_iff_rpow_eq] <;> (try linarith)
              linarith
            linarith
          linarith
        linarith
      · -- a < 5
        have h3 : a < 5 := by
          have h4 : logb 2 (( (a + 1) / 2 - 1 ) ) < 1 := h11
          have h14 : ( (a + 1) / 2 - 1 ) < (2 : ℝ) := by
            by_contra h
            push_neg at h
            have h11 : logb 2 (( (a + 1) / 2 - 1 ) ) ≥ (1 : ℝ) := by
              have h8 : ( (a + 1) / 2 - 1 ) ≥ (2 : ℝ) := by
                linarith
              have h9 : logb 2 (( (a + 1) / 2 - 1 ) ) ≥ logb 2 (2 : ℝ) := by
                apply Real.logb_le_logb_of_le
                all_goals
                  nlinarith
              have h10 : logb 2 (2 : ℝ) = 1 := by
                norm_num [logb_self_eq_one]
              linarith
            linarith
          nlinarith
        linarith
    · -- Assume a ∈ (-1, 5)
      rintro ⟨ha1, ha2⟩
      constructor
      · -- $\log_2(x-1) < 1$
        have h1 : logb 2 (( (a + 1) / 2 - 1 ) ) < 1 := by
          have h3 : ( (a + 1) / 2 - 1 ) > 0 := by
            nlinarith
          have h4 : ( (a + 1) / 2 - 1 ) < (2 : ℝ) := by
            nlinarith
          have h2 : logb 2 (( (a + 1) / 2 - 1 ) ) < 1 := by
            have h10 : ( (a + 1) / 2 - 1 ) < (2 : ℝ) := h4
            have h11 : logb 2 (( (a + 1) / 2 - 1 ) ) < logb 2 (2 : ℝ) := by
              apply Real.logb_lt_logb
              all_goals
                nlinarith
            have h13 : logb 2 (2 : ℝ) = 1 := by
              norm_num [logb_self_eq_one]
            linarith
          linarith
        simpa using h1
      · -- $|x - a| < 2$
        have h2 : |( (a + 1) / 2 ) - a| < 2 := by
          rw [abs_lt]
          constructor
          · -- -2 < ( (a + 1) / 2 ) - a
            nlinarith
          · -- ( (a + 1) / 2 ) - a < 2
            nlinarith
        simpa using h2