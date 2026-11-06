import Mathlib

theorem algebra_296923 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 * (a - 1) + b^2 * (b - 1) + c^2 * (c - 1) = a * (a - 1) + b * (b - 1) + c * (c - 1)) :
    1956 * a^2 + 1986 * b^2 + 2016 * c^2 = 5958 := by
  have h1 : a * (a - 1) ^ 2 + b * (b - 1) ^ 2 + c * (c - 1) ^ 2 = 0 := by
    nlinarith 
  have h2 : a * (a - 1) ^ 2 ≥ 0 := by
    apply mul_nonneg
    linarith
    apply pow_two_nonneg
  have h3 : b * (b - 1) ^ 2 ≥ 0 := by
    apply mul_nonneg
    linarith
    apply pow_two_nonneg
  have h4 : c * (c - 1) ^ 2 ≥ 0 := by
    apply mul_nonneg
    linarith
    apply pow_two_nonneg
  have h5 : a * (a - 1) ^ 2 = 0 := by linarith [h1, h2, h3, h4]
  have h6 : b * (b - 1) ^ 2 = 0 := by linarith [h1, h2, h3, h4]
  have h7 : c * (c - 1) ^ 2 = 0 := by linarith [h1, h2, h3, h4]
  have ha1 : a = 1 := by
    have h8 : (a - 1) ^ 2 = 0 := by 
      apply (mul_eq_zero.mp h5).resolve_left 
      linarith
    have h9 : a - 1 = 0 := by 
      rw [sq_eq_zero_iff] at h8
      exact h8
    linarith
  have hb1 : b = 1 := by
    have h8 : (b - 1) ^ 2 = 0 := by 
      apply (mul_eq_zero.mp h6).resolve_left 
      linarith
    have h9 : b - 1 = 0 := by 
      rw [sq_eq_zero_iff] at h8
      exact h8
    linarith
  have hc1 : c = 1 := by
    have h8 : (c - 1) ^ 2 = 0 := by 
      apply (mul_eq_zero.mp h7).resolve_left 
      linarith
    have h9 : c - 1 = 0 := by 
      rw [sq_eq_zero_iff] at h8
      exact h8
    linarith
  rw [ha1, hb1, hc1]
  norm_num