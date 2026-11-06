import Mathlib

theorem algebra_16297 {a b : ℤ} (h : ∀ x, 16*x^2-106*x-105 = (8*x+a)*(2*x+b)) :
    a + 2*b = -23 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h (-1)
  have eq4 := h 2
  norm_num at eq1 eq2 eq3 eq4
  have h1 : a * b = -105 := by 
    nlinarith
  have h2 : 4 * b + a = -53 := by 
    nlinarith [eq3, eq4, h1]
  have h3 : a = -53 - 4 * b := by
    linarith
  rw [h3] at h1
  have h4 : 4 * b ^ 2 + 53 * b - 105 = 0 := by
    nlinarith
  have h5 : (b + 15) * (4 * b - 7) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- b + 15 = 0, so b = -15
    have hb : b = -15 := by linarith
    have ha : a = 7 := by
      rw [hb] at h3
      linarith
    linarith [hb, ha]
  · -- 4 * b - 7 = 0 → b = 7/4 which is not integer
    have h10 : 4 * b = 7 := by linarith 
    by_cases h : b ≥ 2
    · -- if b ≥ 2 
      nlinarith 
    · -- if b < 2, then since b is integer, b ≤ 1 
      have : b ≤ 1 := by 
        omega 
      nlinarith