import Mathlib

theorem algebra_5029 {x1 x2 : ℝ} (hx1 : 2*x1^2+17*x1+12=5*x1+7) (hx2 : 2*x2^2+17*x2+12=5*x2+7)
    (hxy : x1≠x2) : Real.sqrt ((x2-x1)^2+(5*x2-5*x1)^2) = 26 := by
  have h1 : 2 * x1 ^ 2 + 12 * x1 + 5 = 0 := by
    nlinarith
  have h2 : 2 * x2 ^ 2 + 12 * x2 + 5 = 0 := by
    nlinarith
  have h4 : (x1 - x2) * (2 * (x1 + x2) + 12) = 0 := by
    nlinarith [h1, h2]
  cases (mul_eq_zero.mp h4) with
  | inl h4' =>
    exfalso
    have h5 : x1 = x2 := by linarith
    contradiction
  | inr h4' =>
    have h5 : x1 + x2 = -6 := by
      linarith
    have h7 : (5 * x2 - 5 * x1) = 5 * (x2 - x1) := by
      ring
    have h8 : (x2 - x1) ^ 2 + (5 * x2 - 5 * x1) ^ 2 = (26 : ℝ) * (x2 - x1) ^ 2 := by
      rw [h7]
      nlinarith [sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by
        intro h
        apply hxy
        linarith
      )]
    have h9 : (x2 - x1) ^ 2 = (26 : ℝ) := by
      nlinarith [sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by
        intro h
        apply hxy
        linarith
      ), Real.sqrt_pos.mpr (show (0 : ℝ) < (26 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (26 : ℝ) by norm_num)]
    have h12 : (x2 - x1) ^ 2 + (5 * x2 - 5 * x1) ^ 2 = (676 : ℝ) := by
      nlinarith [h8, h9]
    rw [h12]
    have h14 : Real.sqrt ((676 : ℝ)) = (26 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> nlinarith
    rw [h14]
    <;> norm_num
    <;> nlinarith
    all_goals norm_num
    all_goals nlinarith
    all_goals norm_num