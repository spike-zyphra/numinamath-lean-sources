import Mathlib

theorem algebra_292734 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h₂ : (a^2 - a - c)/(b : ℚ) + (b^2 - b - c)/(a : ℚ) = a + b + 2) :
    IsSquare (a + b + c) := by
  have h₃ : (a : ℚ) > 0 := by exact_mod_cast ha
  have h₄ : (b : ℚ) > 0 := by exact_mod_cast hb
  have h₅ : (a : ℚ) * (a^2 - (a : ℚ) - (c : ℚ)) + (b : ℚ) * (b^2 - (b : ℚ) - (c : ℚ)) = (a * b : ℚ) * (a + b + 2) := by
    field_simp at h₂ ⊢
    nlinarith [h₂, mul_pos h₃ h₄]
  have h₆ : (a : ℤ) * (a^2 - a - c) + (b : ℤ) * (b^2 - b - c) = (a * b : ℤ) * (a + b + 2) := by 
    exact_mod_cast h₅
  have h₇ : a^3 + b^3 - a^2 - b^2 - a * c - b * c - a^2 * b - a * b^2 - 2 * a * b = 0 := by 
    nlinarith [h₆]
  have h₈ : (a + b) * ((a - b) ^ 2) = (a + b) * (a + b + c) := by
    nlinarith [h₇]
  have h9 : (a - b) ^ 2 = a + b + c := by
    have h10 : a + b > 0 := by
      omega
    have h11 : (a + b) * ((a - b) ^ 2) = (a + b) * (a + b + c) := by 
      linarith [h₈]
    have h12 : (a - b) ^ 2 = a + b + c := by
      apply (mul_left_inj' (show a + b ≠ 0 by linarith)).mp
      linarith
    linarith
  have h11 : IsSquare (a + b + c) := by
    use a - b
    linarith [h9]
  exact_mod_cast h11