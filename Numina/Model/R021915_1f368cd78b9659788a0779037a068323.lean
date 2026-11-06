import Mathlib

theorem algebra_150502 {x : ℝ} (hx : x > 0) :
    x ^ Real.logb 5 (0.008 * x) = 125 / x ^ 5 ↔ x = 5 ∨ x = 1 / 125 := by
  constructor
  · -- Forward direction: if x^(log_5(0.008*x)) = 125/x^5, then x = 5 or x = 1/125
    intro h
    have h1 : 0 < x := hx
    have h2 : Real.logb 5 (x ^ Real.logb 5 (0.008 * x)) = Real.logb 5 (125 / x ^ 5) := by
      rw [h]
    have h3 : Real.logb 5 (x ^ Real.logb 5 (0.008 * x)) = Real.logb 5 (0.008 * x) * Real.logb 5 x := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals
        linarith
    have h4 : Real.logb 5 (125 / x ^ 5) = Real.logb 5 (125) - Real.logb 5 (x ^ 5) := by
      rw [Real.logb_div (by positivity) (by positivity)]
    have h5 : Real.logb 5 (125) = 3 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    have h6 : Real.logb 5 (x ^ 5) = 5 * Real.logb 5 x := by
      simp [Real.logb_pow]
    rw [h3, h4, h5, h6] at h2
    have h7 : Real.logb 5 (0.008 * x) = Real.logb 5 (0.008) + Real.logb 5 x := by
      rw [Real.logb_mul (by norm_num) (by linarith)]
    have h8 : Real.logb 5 (0.008) = -3 := by
      have : (0.008 : ℝ) = (5 : ℝ) ^ (-3 : ℝ) := by norm_num
      rw [this]
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals
        norm_num
    rw [h7, h8] at h2
    have h9 : (Real.logb 5 x) ^ 2 + 2 * Real.logb 5 x - 3 = 0 := by
      nlinarith
    have h10 : Real.logb 5 x = 1 ∨ Real.logb 5 x = -3 := by
      have h11 : (Real.logb 5 x - 1) * (Real.logb 5 x + 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h11) with h12 h13
      · -- Real.logb 5 x - 1 = 0
        left
        linarith
      · -- Real.logb 5 x + 3 = 0
        right
        linarith
    cases h10 with
    | inl h11 =>
      have h12 : x = 5 := by
        have h13 : x = (5 : ℝ) ^ (Real.logb 5 x : ℝ) := by
          field_simp
        rw [h13, h11]
        norm_num
      left
      exact h12
    | inr h11 =>
      have h14 : x = (1 / 125) := by
        have h15 : x = (5 : ℝ) ^ (Real.logb 5 x : ℝ) := by
          field_simp
        rw [h15, h11]
        norm_num
      right
      exact h14
  · -- Backward direction: x = 5 or x = 1/125 then x^(log_5(0.008*x)) = 125/x^5
    intro h
    cases h with
    | inl h1 =>
      rw [show x = (5 : ℝ) by linarith]
      have h2 : (5 : ℝ) ^ Real.logb 5 (0.008 * (5 : ℝ)) = (125 / (5 : ℝ) ^ 5) := by
        have h3 : Real.logb 5 (0.008 * (5 : ℝ)) = Real.logb 5 (0.04) := by
          norm_num
        have h4 : Real.logb 5 (0.04) = -2 := by
          have : (0.04 : ℝ) = (5 : ℝ) ^ (-2 : ℝ) := by norm_num
          rw [this]
          rw [Real.logb_rpow_eq_mul_logb_of_pos]
          all_goals
            norm_num
        rw [h3, h4]
        norm_num
      linarith [h2]
    | inr h1 =>
      rw [show x = (1 / 125 : ℝ) by linarith]
      have h2 : (1 / 125 : ℝ) ^ Real.logb 5 (0.008 * (1 / 125 : ℝ)) = (125 / (1 / 125 : ℝ) ^ 5) := by
        have h3 : Real.logb 5 (0.008 * (1 / 125 : ℝ)) = -6 := by
          have h4 : (0.008 * (1 / 125 : ℝ)) = (5 : ℝ) ^ (-6 : ℝ) := by norm_num
          rw [h4]
          rw [Real.logb_rpow_eq_mul_logb_of_pos]
          all_goals
            norm_num
        rw [h3]
        norm_num
      linarith [h2]