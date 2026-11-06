import Mathlib

open Real Set

theorem algebra_227988 (a : ℝ) (ha : 0 < a ∧ a ≠ 1) :
    logb a (2 / 3) < 1 ↔ (0 < a ∧ a < 2 / 3) ∨ (1 < a) := by
  have h1 : 0 < a := ha.1
  have h2 : a ≠ 1 := ha.2
  have h3 : logb a (2 / 3) = (log (2 / 3) ) / (log a) := by 
    field_simp [logb]

  rw [h3]

  by_cases h4 : a > 1 
  · -- Case $a > 1$ (so logarithm is strictly increasing)
    have h5 : log a > 0 := by 
      apply log_pos
      all_goals linarith

    have h6 : (log (2 / 3) ) / (log a) < 1 ↔ (log (2 / 3) < log a) := by 
      constructor
      · -- Assume (log (2/3) ) / (log a) < 1 prove log (2/3) < log a
        intro h 
        have h7 : log a > 0 := h5 
        apply (div_lt_iff₀ (by linarith)).mp at h 
        linarith 
      · -- Assume log (2/3) < log a prove (log (2/3) ) / (log a) < 1
        intro h 
        have h7 : log a > 0 := h5 
        apply (div_lt_iff₀ (by linarith)).mpr 
        linarith

    rw [h6]
    have h7 : log (2 / 3) < log a := by 
      have h8 : (2 / 3 : ℝ) < a := by 
        nlinarith 
      have h9 : log (2 / 3) < log a := by 
        apply Real.log_lt_log 
        all_goals 
          try linarith 
      linarith

    constructor 
    · -- Forward: if log (2/3) < log a, prove the right side 
      intro h 
      right 
      linarith
    · -- Backward: if the right side is true, prove log (2/3) < log a 
      intro h
      cases h with
      | inl h1l =>
        linarith -- This case is impossible given a > 1
      | inr h2r =>
        linarith -- This should derive from a > 1

  · -- Case $a \le 1$. Since $a > 0$ and $a \ne 1$, we must have $0 < a < 1$.
    have h4' : a ≤ 1 := by linarith
    have h5 : a < 1 := by 
      by_contra h
      push_neg at h
      have hge1 : a ≥ 1 := by linarith 
      have hne1 : a ≠ 1 := h2
      have hgt1 : a > 1 := by 
        by_contra h'
        push_neg at h'
        have heq1 : a = 1 := by linarith 
        tauto 
      nlinarith

    have h6 : log a < 0 := by 
      have h7 : a < 1 := h5 
      have h8 : log a < 0 := by 
        have h9 : a < 1 := h7 
        have h10 : log a < log (1 : ℝ) := by 
          apply Real.log_lt_log 
          all_goals 
            nlinarith 
        have h11 : log (1 : ℝ) = 0 := Real.log_one 
        linarith 
      linarith

    have h7 : (log (2 / 3) ) / (log a) < 1 ↔ (log (2 / 3) > log a) := by 
      constructor 
      · -- Assume (log (2/3) ) / (log a) < 1 prove log (2/3) > log a 
        intro h 
        have h8 : log a < 0 := h6 
        apply (div_lt_iff_of_neg' (by linarith)).mp at h 
        linarith 
      · -- Assume log (2/3) > log a prove (log (2/3) ) / (log a) < 1 
        intro h 
        have h8 : log a < 0 := h6 
        apply (div_lt_iff_of_neg' (by linarith)).mpr 
        linarith

    rw [h7]

    have h81 : log (2 / 3) < (0 : ℝ) := by 
      have : (2 / 3 : ℝ) < 1 := by norm_num 
      have h9 : log (2 / 3) < log (1 : ℝ) := by 
        apply Real.log_lt_log 
        all_goals 
          try linarith 
      have h10 : log (1 : ℝ) = 0 := Real.log_one 
      linarith

    constructor 
    · -- Forward implication: from `log (2/3) > log a` prove RHS 
      intro h 
      left 
      constructor 
      · linarith 
      · -- Show $a < 2/3$ 
        by_contra h9 
        push_neg at h9 
        have h11 : a ≥ (2 / 3 : ℝ) := by linarith 
        have h12 : log a ≥ log (2 / 3) := by 
          have h13 : (2 / 3 : ℝ) ≤ a := by linarith 
          have h14 : a < (1 : ℝ) := by linarith 
          have h15 : (2 / 3 : ℝ) < (1 : ℝ) := by norm_num 
          have h16 : a < (1 : ℝ) := by linarith 
          -- Since logarithm is strictly increasing, but here for $a \in (0, 1)$ we need to verify
          -- This part expansion would be messy for general cases
          -- Applying the specific current facts
          have h17 : log (2 / 3) < (0 : ℝ) := h81 
          have h18 : log a < (0 : ℝ) := h6 
          have : log a ≥ log (2 / 3) := by 
            have h19 : a ≥ (2 / 3 : ℝ) := h11 
            have h20 : (2 / 3 : ℝ) > 0 := by norm_num 
            have h21 : a > 0 := by linarith 
            have h22 : log a ≥ log (2 / 3) := by 
              apply Real.log_le_log 
              all_goals 
                try linarith 
            linarith 
          linarith 
        linarith -- This would have shown inconsistency from h > 0.

    · -- Backward implication: from RHS prove `log (2/3) > log a`
      intro h 
      cases h with 
      | inl h1l =>
        have h11 : a < (2 / 3 : ℝ) := by 
          linarith 
        -- Similar code to prove `log (2/3) > log a`. Is `linarith`.
        have h33 : log (2 / 3) > log a := by 
          have h9 : a < (2 / 3 : ℝ) := h11 
          have h10 : log a < log (2 / 3) := by 
            apply Real.log_lt_log 
            all_goals 
              try linarith 
          linarith 
        linarith 
      | inr h2r =>
        -- This is impossible: a < 1 contradicts 1 < a.
        nlinarith