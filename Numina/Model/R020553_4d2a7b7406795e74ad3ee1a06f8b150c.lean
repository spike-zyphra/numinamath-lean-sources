import Mathlib

theorem algebra_95314 (x : ℝ) (hx : x > 0) :
    2 * Real.sqrt x + 2 * x ^ (-1 / 2 : ℝ) = 5 ↔ 4 * x ^ 2 - 17 * x + 4 = 0 := by
  constructor
  · -- Forward direction: 2 * sqrt(x) + 2 * x^(-1/2) = 5 → 4x^2 -17x +4 =0
    intro h
    have h1 : x ^ (-1 / 2 : ℝ) = 1 / Real.sqrt x := by
      have h2 : x ^ (-1 / 2 : ℝ) = (x ^ (1 / 2 : ℝ)) ^ (-1 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals linarith
      rw [h2]
      have h3 : (x ^ (1 / 2 : ℝ) : ℝ) = Real.sqrt x := by
        rw [Real.sqrt_eq_rpow]
      rw [h3]
      simp [Real.sqrt_eq_rpow]
      <;> simp [Real.rpow_neg_one, one_div, pow_two]
      all_goals tauto
    rw [h1] at h
    have h2 : Real.sqrt x > 0 := by
      apply Real.sqrt_pos.2
      exact hx
    have h3 : 2 * (Real.sqrt x) ^ 2 + 2 = 5 * Real.sqrt x := by
      have h4 : Real.sqrt x > 0 := h2
      field_simp [h4] at h ⊢
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
    have h4 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
  · -- Backward direction: 4x^2 -17x +4 =0 → 2 * sqrt(x) + 2 * x^(-1/2) = 5
    intro h
    have h1 : x ^ (-1 / 2 : ℝ) = 1 / Real.sqrt x := by
      have h2 : x ^ (-1 / 2 : ℝ) = (x ^ (1 / 2 : ℝ)) ^ (-1 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals linarith
      rw [h2]
      have h3 : (x ^ (1 / 2 : ℝ) : ℝ) = Real.sqrt x := by
        rw [Real.sqrt_eq_rpow]
      rw [h3]
      simp [Real.sqrt_eq_rpow]
      <;> simp [Real.rpow_neg_one, one_div, pow_two]
      all_goals tauto
    rw [h1]
    have h2 : Real.sqrt x > 0 := by
      apply Real.sqrt_pos.2
      exact hx
    have h3 : 2 * (Real.sqrt x) ^ 2 + 2 = 5 * Real.sqrt x := by
      have h4 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
      nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
    have h4 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
    field_simp [h2, h4]
    <;> nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]