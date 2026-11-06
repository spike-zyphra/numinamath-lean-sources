import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_301818 {a : ℝ} (ha : 0 < a) (h : ∃ x1 x2 : ℝ,
    x1 ∈ Ioo 1 3 ∧ x2 ∈ Ioi 6 ∧
    x1^2 - 4 * x1 * logb 2 a + 3 * (logb 2 a)^2 = 0 ∧
    x2^2 - 4 * x2 * logb 2 a + 3 * (logb 2 a)^2 = 0) :
    4 < a ∧ a < 8 := by
  rcases h with ⟨x1, x2, hx1, hx2, h1, h2⟩
  rcases hx1 with ⟨h1a, h1b⟩
  have h2a : 6 < x2 := by 
    simpa using hx2

  have h_eq1 : (x1 - logb 2 a) * (x1 - 3 * logb 2 a) = 0 := by 
    nlinarith
  have h_eq2 : (x2 - logb 2 a) * (x2 - 3 * logb 2 a) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h_eq1) with h_eq1_left h_eq1_right
  · -- Case where x1 = logb 2 a
    cases' (mul_eq_zero.mp h_eq2) with h_eq2_left h_eq2_right
    · -- Case where x2 = logb 2 a
      exfalso
      nlinarith
    · -- Case where x2 = 3 * logb 2 a
      have h5 : 2 ≤ logb 2 a := by
        nlinarith
      have h6 : logb 2 a < (3 : ℝ) := by
        nlinarith
      constructor
      · -- Show 4 < a
        have h7 : 4 < a := by
          have h8 : logb 2 a ≥ (2 : ℝ) := by
            nlinarith
          have h10 : (2 : ℝ) < (4 : ℝ) := by norm_num 
          have h11 : a > (0 : ℝ) := by
            linarith
          have h12 : a > (4 : ℝ) := by
            by_contra h
            push_neg at h 
            have h13 : a ≤ (4 : ℝ) := by
              nlinarith 
            have h14 : logb 2 a ≤ (2 : ℝ) := by
              have h17 : logb 2 a = Real.logb 2 a := by
                simp 
              rw [h17] 
              have h11 : a ≤ (4 : ℝ) := by
                nlinarith 
              have : Real.logb 2 a ≤ (2 : ℝ) := by
                have h22 : Real.logb (2 : ℝ) a ≤ Real.logb (2 : ℝ) (4 : ℝ) := by
                  apply Real.logb_le_logb_of_le 
                  all_goals 
                    nlinarith 
                have h11a : Real.logb (2 : ℝ) (4 : ℝ) = (2 : ℝ) := by 
                  rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
                nlinarith [h22, h11a] 
              nlinarith 
            nlinarith 
          linarith 
        linarith 
      · -- Show a < 8
        have h8 : a < (8 : ℝ) := by
          have h6 : logb 2 a < (3 : ℝ) := by
            nlinarith
          have h11 : a > (0 : ℝ) := by
            linarith 
          by_contra h
          push_neg at h 
          have h13 : a ≥ (8 : ℝ) := by
            nlinarith 
          have h14 : logb 2 a ≥ (3 : ℝ) := by
            have h17 : logb 2 a = Real.logb 2 a := by
              simp 
            rw [h17] 
            have h11 : a ≥ (8 : ℝ) := by
              nlinarith 
            have : Real.logb 2 a ≥ (3 : ℝ) := by
              have h22 : Real.logb (2 : ℝ) a ≥ Real.logb (2 : ℝ) (8 : ℝ) := by
                apply Real.logb_le_logb_of_le 
                all_goals 
                  nlinarith 
              have h11a : Real.logb (2 : ℝ) (8 : ℝ) = (3 : ℝ) := by
                rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
              nlinarith [h22, h11a] 
            nlinarith 
          nlinarith 
        linarith 
  · -- Case where x1 = 3 * logb 2 a
    cases' (mul_eq_zero.mp h_eq2) with h_eq2_left h_eq2_right
    · -- Case where x2 = logb 2 a
      exfalso
      nlinarith
    · -- Case where x2 = 3 * logb 2 a
      exfalso 
      nlinarith