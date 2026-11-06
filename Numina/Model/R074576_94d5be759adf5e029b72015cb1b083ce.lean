import Mathlib

theorem algebra_1438
    (a b c d e f : ℚ)
    (h₀ : a + b + 6 = c + d + e)
    (h₁ : a + c + f = b + d + 7)
    (h₂ : a + d + e = b + c + f)
    (h₃ : a + e + f = b + d + c)
    (h₄ : a + f + 7 = b + e + d)
    (h₅ : a + 6 + 7 = b + c + e) :
    (a * b + c * d + e * f) / (a + b + c + d + e + f) = 11 / 12 := by
  have h6 : a + b + c + d + e + f ≠ 0 := by
    by_contra h
    have h7 : a + b + c + d + e + f = 0 := by linarith
    nlinarith
    all_goals assumption
    all_goals nlinarith
  have h_eq1 : a * b + c * d + e * f = 11 := by
    nlinarith
  have eq2 : a + b + c + d + e + f = 12 := by 
    nlinarith
  have h_eq2 : a + b + c + d + e + f = 12 := eq2
  rw [h_eq2]
  field_simp [show (12 : ℚ) ≠ 0 by norm_num]
  nlinarith
  all_goals norm_num