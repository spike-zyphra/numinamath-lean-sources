import Mathlib

theorem algebra_262623 (a : ℝ) :
    ∃ x : ℝ, 10^(x^2 + 4*x + 1) = a ↔ a ≥ 1/1000 := by 
  by_cases h : a ≥ 1 / 1000
  · -- Assume a ≥ 1/1000, prove ∃ x, (10:ℝ)^(x^2 + 4*x + 1) = a ↔ a ≥ 1/1000
    use -2 + Real.sqrt (3 + Real.logb 10 a)
    have h4 : Real.logb 10 a ≥ -3 := by
      have h5 : a ≥ 1 / 1000 := h
      have h6 : Real.logb 10 a ≥ Real.logb 10 (1 / 1000 : ℝ) := by
        apply Real.logb_le_logb_of_le
        all_goals linarith [show (0 : ℝ) < 1 / 1000 by norm_num, show 0 < (a : ℝ) by linarith [h]]
      have h7 : Real.logb 10 (1 / 1000 : ℝ) = -3 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        <;> norm_num
      linarith [h7, h6]
    have h8 : Real.sqrt (3 + Real.logb 10 a) ^ 2 = 3 + Real.logb 10 a := by
      rw [Real.sq_sqrt]
      linarith
    have h9 : (-2 + Real.sqrt (3 + Real.logb 10 a)) ^ 2 + 4 * (-2 + Real.sqrt (3 + Real.logb 10 a)) + 1 = Real.logb 10 a := by
      nlinarith [h8, h4]
    have h10 : (10 : ℝ) ^ ((-2 + Real.sqrt (3 + Real.logb 10 a)) ^ 2 + 4 * (-2 + Real.sqrt (3 + Real.logb 10 a)) + 1 : ℝ) = (10 : ℝ) ^ (Real.logb 10 a : ℝ) := by
      rw [h9]
    have h11 : (10 : ℝ) ^ (Real.logb 10 a : ℝ) = a := by
      rw [Real.rpow_logb]
      all_goals linarith
    rw [h10]
    rw [h11]
    all_goals tauto
  · -- Assume ¬(a ≥ 1/1000), need to prove ∃ x, (10:ℝ)^(x^2 + 4*x + 1) = a ↔ a ≥ 1/1000
    push_neg at h
    use -2
    have hx : (10 : ℝ) ^ ((-2 : ℝ) ^ 2 + 4 * (-2) + 1 : ℝ) = (1 / 1000 : ℝ) := by
      rw [show (-2 : ℝ) ^ 2 + 4 * (-2) + 1 = (-3 : ℝ) by norm_num]
      norm_num
      <;> norm_num
    rw [hx]
    constructor
    · -- Show that 1/1000 = a → contradiction (since a < 1/1000)
      intro h_eq
      linarith
    · -- Show that a ≥ 1/1000 → contradiction (since a < 1/1000)
      intro h_ge
      linarith