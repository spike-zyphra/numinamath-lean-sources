import Mathlib

theorem algebra_11797 {x y : ℝ} (hx : 0 < x) (hy : x < y) (h : x / y + y / x = 6) :
    (x + y) / (x - y) = -Real.sqrt 2 := by
  have h1 : 0 < y := by linarith
  have h2 : x / y + y / x = 6 := h
  have eq1 : x ^ 2 + y ^ 2 = 6 * x * y := by
    have h3 : y ≠ 0 := by linarith
    have h4 : x ≠ 0 := by linarith
    field_simp [h3, h4] at h2
    nlinarith
  have eq2 : ((x + y) / (x - y)) ^ 2 = 2 := by
    have h5 : x - y ≠ 0 := by linarith
    have eq3 : ((x + y) / (x - y)) ^ 2 = ((x + y) ^ 2) / ((x - y) ^ 2) := by
      field_simp [h5]
    rw [eq3]
    have eq4 : (x + y) ^ 2 = 8 * x * y := by
      nlinarith [eq1]
    have eq5 : (x - y) ^ 2 = 4 * x * y := by
      nlinarith [eq1]
    rw [eq4, eq5]
    have h6 : 4 * x * y ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      linarith
      linarith
      all_goals linarith
    field_simp [show x ≠ 0 by linarith, show y ≠ 0 by linarith]
    <;> nlinarith
  have h3 : (x + y) / (x - y) < 0 := by
    have h4 : x - y < 0 := by linarith
    have h5 : x + y > 0 := by linarith
    apply div_neg_of_pos_of_neg
    all_goals linarith
  have h4 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
  have eq3 : (x + y) / (x - y) = -Real.sqrt 2 := by
    have h5 : ((x + y) / (x - y)) ^ 2 = 2 := eq2
    have h6 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h7 : ( (x + y) / (x - y) ) ^ 2 = (Real.sqrt 2) ^ 2 := by
      linarith [h5, h6]
    have h8 : ( (x + y) / (x - y) ) = Real.sqrt 2 ∨ ( (x + y) / (x - y) ) = - (Real.sqrt 2) := by
      apply eq_or_eq_neg_of_sq_eq_sq
      all_goals
      nlinarith [h7]
    cases h8 with
    | inl h9 =>
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), h3, h9]
    | inr h10 =>
      linarith
  exact eq3