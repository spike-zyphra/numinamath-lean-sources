import Mathlib

theorem algebra_57145 {a b c : ℤ} (h₀ : 2 * a + 3 * b = 52) (h₁ : 3 * b + c = 41)
    (h₂ : b * c = 60) : a + b + c = 25 := by
  have hc : c = 41 - 3 * b := by
    linarith
  rw [hc] at h₂
  have h3 : 3 * b ^ 2 - 41 * b + 60 = 0 := by 
    nlinarith
  have : (b - 12) * (3 * b - 5) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp this) with hb1 hb2
  · -- Case 1: b - 12 = 0, so b = 12
    have hb : b = 12 := by linarith
    have ha : a = 8 := by 
      rw [hb] at h₀ 
      linarith 
    have hc2 : c = 5 := by 
      rw [hb] at hc 
      linarith 
    linarith [ha, hb, hc2] 
  · -- Case 2: 3b - 5 = 0, which is not integer, so invalid
    have h4 : 3 * b = 5 := by linarith 
    have : b % 3 = 0 := by 
      omega 
    omega