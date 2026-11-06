import Mathlib

theorem algebra_96892 (a b : ℝ) (h : ∃ x1 x2 x3 : ℝ, x1 > 0 ∧ x2 > 0 ∧ x3 > 0 ∧ x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x1 ∧
    8*x1^3+4*a*x1^2+2*b*x1+a=0 ∧ 8*x2^3+4*a*x2^2+2*b*x2+a=0 ∧ 8*x3^3+4*a*x3^2+2*b*x3+a=0 ∧
    Real.logb 2 x1+Real.logb 2 x2+Real.logb 2 x3=5) :
    a=-256 := by

  rcases h with ⟨x1, x2, x3, hx1, hx2, hx3, h12, h23, h31, h_eq1, h_eq2, h_eq3, h_log⟩
  have h1 : Real.logb 2 x1 + Real.logb 2 x2 + Real.logb 2 x3 = Real.logb 2 (x1 * x2 * x3) := by
    rw [← Real.logb_mul (by positivity) (by positivity)]
    rw [← Real.logb_mul (by positivity) (by positivity)]

  have h2 : x1 * x2 * x3 = (32 : ℝ) := by
    have h3 : Real.logb 2 (x1 * x2 * x3) = (5 : ℝ) := by linarith [h_log, h1]
    have h4 : x1 * x2 * x3 = (2 : ℝ) ^ (5 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by positivity) ] at h3
      · linarith
      all_goals linarith
    rw [h4]
    norm_num

  have eq1 : 8 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) + 4 * a * (x1 + x2) + 2 * b = 0 := by
    have h12' : x1 - x2 ≠ 0 := by
      intro h'
      apply h12
      linarith
    have eq_sub : (x1 - x2) * (8 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) + 4 * a * (x1 + x2) + 2 * b) = 0 := by
      nlinarith [h_eq1, h_eq2, sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by intro h'; apply h12; linarith)]
    cases' (mul_eq_zero.mp eq_sub) with h5 h6
    · -- x1 - x2 ≠ 0
      exfalso
      apply h12
      linarith
    · -- The second factor must be zero
      linarith

  have eq2 : 8 * (x2 ^ 2 + x2 * x3 + x3 ^ 2) + 4 * a * (x2 + x3) + 2 * b = 0 := by
    have h23' : x2 - x3 ≠ 0 := by
      intro h'
      apply h23
      linarith
    have eq_sub : (x2 - x3) * (8 * (x2 ^ 2 + x2 * x3 + x3 ^ 2) + 4 * a * (x2 + x3) + 2 * b) = 0 := by
      nlinarith [h_eq2, h_eq3, sq_pos_of_ne_zero (show x2 - x3 ≠ 0 by intro h'; apply h23; linarith)]
    cases' (mul_eq_zero.mp eq_sub) with h5 h6
    · -- x2 - x3 ≠ 0
      exfalso
      apply h23
      linarith
    · -- The second factor must be zero
      linarith

  have eq3 : 4 * (x1 - x3) * (2 * (x1 + x2 + x3) + a) = 0 := by
    nlinarith [eq1, eq2]

  have h13 : x1 - x3 ≠ 0 := by 
    intro h'
    apply h31
    linarith

  have eq4 : 2 * (x1 + x2 + x3) + a = 0 := by
    apply (mul_left_inj' h13).mp
    linarith

  have eq5 : a = -2 * (x1 + x2 + x3) := by linarith

  have eq8 : a = -256 := by
    have eq9 : x1 + x2 + x3 = (128 : ℝ) := by
      nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x2 - x3), sq_nonneg (x3 - x1), mul_pos hx1 hx2, mul_pos hx2 hx3, mul_pos hx1 hx3, h2, eq5]
    rw [eq9] at eq5
    linarith
  exact eq8