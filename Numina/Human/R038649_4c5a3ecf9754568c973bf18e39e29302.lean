import Mathlib

theorem algebra_249327 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * ((a + b) / 2 - c) + b * c * ((b + c) / 2 - a) +
      a * c * ((c + a) / 2 - b) = 0) : a = b ∧ b = c := by 
  have h1 : (a - b) ^ 2 * c + (b - c) ^ 2 * a + (c - a) ^ 2 * b = 0 := by linarith 
  have h2 : (a - b) ^ 2 * c = 0 := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), ha, hb, hc]
  have hab : a = b := by 
    have : (a - b) ^ 2 = 0 := by 
      apply (mul_eq_zero.mp h2).resolve_right
      linarith
    have : a - b = 0 := pow_eq_zero this
    linarith
  have h3 : (b - c) ^ 2 * a = 0 := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), ha, hb, hc]
  have hbc : b = c := by 
    have : (b - c) ^ 2 = 0 := by 
      apply (mul_eq_zero.mp h3).resolve_right
      linarith
    have : b - c = 0 := pow_eq_zero this
    linarith
  exact ⟨hab, hbc⟩