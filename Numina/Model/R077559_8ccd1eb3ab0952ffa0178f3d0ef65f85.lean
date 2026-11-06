import Mathlib

theorem algebra_244759 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : (a + b) / 2 + 2 / (1 / a + 1 / b) = a - b) :
    a / b = 3 + 2 * √3 := by
  have h1 : 1 / a + 1 / b = (a + b) / (a * b) := by
    field_simp
    <;> ring
  have h2 : 2 / (1 / a + 1 / b) = 2 * (a * b) / (a + b) := by
    rw [h1]
    field_simp
    <;> ring_nf <;> field_simp
    all_goals linarith
  rw [h2] at h
  have h3 : 0 < a * b := by
    apply mul_pos
    exact ha
    exact hb
  have h4 : a + b ≠ 0 := by
    nlinarith
  have h_eq : a ^ 2 + 6 * a * b + b ^ 2 = 2 * (a ^ 2 - b ^ 2) := by
    field_simp [(show a + b ≠ 0 by nlinarith), (show a * b ≠ 0 by positivity)] at h ⊢
    ring_nf at h ⊢
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_pos_of_pos ha, sq_pos_of_pos hb]
    
  have h_eq2 : a ^ 2 - 6 * a * b - 3 * b ^ 2 = 0 := by
    linarith [h_eq]

  have h_eq3 : (a - (3 + 2 * Real.sqrt 3) * b) * (a - (3 - 2 * Real.sqrt 3) * b) = 0 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (a - (3 + 2 * Real.sqrt 3) * b), sq_nonneg (a - (3 - 2 * Real.sqrt 3) * b), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num)]

  cases' (mul_eq_zero.mp h_eq3) with h_eq4 h_eq5
  · -- case where positive solution
    have h_eq5 : a / b = 3 + 2 * Real.sqrt 3 := by
      field_simp [(show b ≠ 0 by linarith [hb]), (show a ≠ 0 by linarith [ha])] at h_eq4 ⊢
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    linarith [h_eq5]
    
  · -- contradiction case where negative solution
    have h_eq6 : a < 0 := by
      have r8 : 3 * (Real.sqrt 3 : ℝ) ^ 2 > 3 * 1 ^ 2  := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ)]
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num)]
    linarith [show 0 < a from ha, h_eq6]