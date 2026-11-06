import Mathlib

theorem algebra_230416 {a : ℝ} (ha : a > 1) (h : (a ^ 3 - (1 / a) ^ 3) = 4 * (a - 1 / a)) :
    a = (1 + Real.sqrt 5) / 2 := by
  have ha2 : a ^ 2 > 1 := by
    nlinarith
  have h1 : a ^ 6 - 4 * a ^ 4 + 4 * a ^ 2 - 1 = 0 := by
    have h2 : a ≠ 0 := by linarith
    have h3 : a ^ 3 > 0 := by positivity
    have eq1 : (a ^ 3 - (1 / a) ^ 3) = 4 * (a - 1 / a) := by linarith
    have eq2 : (a ^ 3 - (1 / a) ^ 3) * a ^ 3 = 4 * (a - 1 / a) * a ^ 3 := by
      rw [eq1]
    have eq3 : (a ^ 3 - (1 / a) ^ 3) * a ^ 3 = a ^ 6 - 1 := by
      field_simp
      <;> ring
    have eq4 : 4 * (a - 1 / a) * a ^ 3 = 4 * (a ^ 4 - a ^ 2) := by
      field_simp
      <;> ring
    rw [eq3, eq4] at eq2
    linarith
  have h2 : (a ^ 2 - 1) * (a ^ 4 - 3 * a ^ 2 + 1) = 0 := by
    nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (a ^ 2 - (3 / 2)), sq_nonneg (a * (a ^ 2 - 1))]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- h3: a^2 - 1 = 0
    have h4 : a ^ 2 = 1 := by linarith
    nlinarith
  · -- h4: a^4 - 3 * a^2 + 1 = 0
    have h6 : (a ^ 2) ^ 2 - 3 * (a ^ 2) + 1 = 0 := by nlinarith
    have h8 : (a ^ 2 - (3 + Real.sqrt 5) / 2) * (a ^ 2 - (3 - Real.sqrt 5) / 2) = 0 := by
      nlinarith [h6, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (a ^ 2 - 3 / 2), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)]
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- h9: a^2 - (3 + Real.sqrt 5) / 2 = 0
      have h11 : a ^ 2 = (3 + Real.sqrt 5) / 2 := by linarith
      have h12 : a > 0 := by nlinarith
      have h13 : a = Real.sqrt ((3 + Real.sqrt 5) / 2) := by
        rw [← h11]
        field_simp [h12]
      have h14 : Real.sqrt ((3 + Real.sqrt 5) / 2) = (1 + Real.sqrt 5) / 2 := by
        have h15 : ((1 + Real.sqrt 5) / 2) ^ 2 = (3 + Real.sqrt 5) / 2 := by
          nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        have h16 : 0 ≤ (3 + Real.sqrt 5) / 2 := by nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        have h17 : 0 ≤ (1 + Real.sqrt 5) / 2 := by nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [h16, h17, h15, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 5]
      rw [h13, h14]
      <;> linarith
    · -- h10: a^2 - (3 - Real.sqrt 5) / 2 = 0
      have h11 : a ^ 2 = (3 - Real.sqrt 5) / 2 := by linarith
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)]