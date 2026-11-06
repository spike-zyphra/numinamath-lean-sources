import Mathlib

open BigOperators Real Set

theorem algebra_630875 :
  IsGreatest {M | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ M = if a * b ≤ 4 / (a ^ 2 + 4 * b ^ 2) then a * b else 4 / (a ^ 2 + 4 * b ^ 2)} 1 := by
  constructor
  · -- Show that 1 is in the set.
    use Real.sqrt 2, Real.sqrt 2 / 2
    constructor
    · -- Show that sqrt(2) > 0
      positivity
    constructor
    · -- Show that sqrt(2)/2 > 0
      positivity
    · -- Show that 1 is obtained
      have h1 : Real.sqrt 2 > 0 := by positivity
      have hab : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
        nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have ha2b2 : Real.sqrt 2 ^ 2 + 4 * (Real.sqrt 2 / 2) ^ 2 = 4 := by
        nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h2 : Real.sqrt 2 * (Real.sqrt 2 / 2) ≤ 4 / (Real.sqrt 2 ^ 2 + 4 * (Real.sqrt 2 / 2) ^ 2) := by
        rw [show Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 by linarith [hab], show Real.sqrt 2 ^ 2 + 4 * (Real.sqrt 2 / 2) ^ 2 = (4 : ℝ) by linarith [ha2b2]]
        all_goals
          norm_num
      rw [if_pos h2]
      all_goals
        linarith [hab]
  · -- Show that 1 is greatest in the set.
    intro M h
    rcases h with ⟨a, b, ha, hb, h_eq⟩
    have h1 : a * b > 0 := mul_pos ha hb
    by_cases h2 : a * b ≤ 4 / (a ^ 2 + 4 * b ^ 2)
    · -- If $a * b \leq 4 / (a ^ 2 + 4 * b ^ 2)$ then $M = a * b$
      have h3 : M = a * b := by
        rw [h_eq]
        simp [h2]
      rw [h3]
      have h4 : a * b ≤ 1 := by
        have h5 : a * b ≤ 4 / (a ^ 2 + 4 * b ^ 2) := h2
        have h6 : a * b * (a ^ 2 + 4 * b ^ 2) ≤ 4 := by
          have h7 : a * b ≤ 4 / (a ^ 2 + 4 * b ^ 2) := h2
          have h8 : a ^ 2 + 4 * b ^ 2 > 0 := by positivity
          have h9 : a * b * (a ^ 2 + 4 * b ^ 2) ≤ 4 := by
            have h10 : a * b ≤ (4 / (a ^ 2 + 4 * b ^ 2) : ℝ) := h2
            have h11 : a * b * (a ^ 2 + 4 * b ^ 2) ≤ (4 / (a ^ 2 + 4 * b ^ 2)) * (a ^ 2 + 4 * b ^ 2) := by
              have h15 : a * b ≤ (4 / (a ^ 2 + 4 * b ^ 2) : ℝ) := h2
              have h16 : a ^ 2 + 4 * b ^ 2 ≥ 0 := by positivity
              nlinarith [h15, show (4 / (a ^ 2 + 4 * b ^ 2) : ℝ) ≥ 0 by positivity]
            have h18 : (4 / (a ^ 2 + 4 * b ^ 2) : ℝ) * (a ^ 2 + 4 * b ^ 2) = 4 := by
              field_simp
            nlinarith
          linarith
        have h8 : a * b * (a ^ 2 + 4 * b ^ 2) ≥ 4 * (a * b) ^ 2 := by
          have h9 : a ^ 2 + 4 * b ^ 2 ≥ 4 * (a * b) := by
            nlinarith [sq_nonneg (a - 2 * b)]
          have h10 : a * b > 0 := by positivity
          nlinarith [sq_nonneg (a * b), mul_pos ha hb]
        have h10 : (a * b) ^ 2 ≤ 1 := by
          nlinarith [h6, h8]
        have h11 : a * b ≤ 1 := by
          nlinarith [show (0 : ℝ) ≤ a * b by positivity]
        linarith
      linarith
    · -- Case where $a * b > 4 / (a ^ 2 + 4 * b ^ 2)$, then $M = 4 / (a ^ 2 + 4 * b ^ 2)$
      have h3 : M = 4 / (a ^ 2 + 4 * b ^ 2) := by
        rw [h_eq]
        simp [h2]
      rw [h3]
      have h4 : 4 / (a ^ 2 + 4 * b ^ 2) ≤ 1 := by
        have h5 : a * b > 4 / (a ^ 2 + 4 * b ^ 2) := by linarith
        have h11 : a ^ 2 + 4 * b ^ 2 ≥ 4 := by
          have h6 : a * b * (a ^ 2 + 4 * b ^ 2) > 4 := by
            have h7 : a * b > 4 / (a ^ 2 + 4 * b ^ 2) := by linarith
            have h8 : a ^ 2 + 4 * b ^ 2 > 0 := by positivity
            have h9 : a * b * (a ^ 2 + 4 * b ^ 2) > 4 := by
              have h10 : a * b > 4 / (a ^ 2 + 4 * b ^ 2) := by linarith
              have h11 : a * b * (a ^ 2 + 4 * b ^ 2) > (4 / (a ^ 2 + 4 * b ^ 2) : ℝ) * (a ^ 2 + 4 * b ^ 2) := by
                apply mul_lt_mul_of_pos_right
                linarith
                positivity
              have h12 : (4 / (a ^ 2 + 4 * b ^ 2) : ℝ) * (a ^ 2 + 4 * b ^ 2) = 4 := by
                field_simp
              nlinarith
            linarith
          have h10 : a ^ 2 + 4 * b ^ 2 ≥ 4 * (a * b) := by
            nlinarith [sq_nonneg (a - 2 * b)]
          nlinarith [sq_nonneg (a ^ 2 + 4 * b ^ 2 - 4), sq_nonneg (a * b - 1), sq_nonneg (a - 2 * b), sq_nonneg (2 * b ^ 2 - 1)]
        have h13 : 4 / (a ^ 2 + 4 * b ^ 2) ≤ 1 := by
          have h14 : a ^ 2 + 4 * b ^ 2 ≥ 4 := h11
          have h15 : a ^ 2 + 4 * b ^ 2 > 0 := by positivity
          apply (div_le_iff₀ (by positivity)).mpr
          nlinarith
        linarith
      linarith