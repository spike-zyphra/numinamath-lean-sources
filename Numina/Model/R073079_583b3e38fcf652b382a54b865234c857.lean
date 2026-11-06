import Mathlib

theorem algebra_206107 :
    ¬∃ a b c d : ℤ, (a * 19 ^ 3 + b * 19 ^ 2 + c * 19 + d = 1) ∧ (a * 62 ^ 3 + b * 62 ^ 2 + c * 62 + d = 2) := by
  rintro ⟨a, b, c, d, h1, h2⟩
  have eq1 : a * 19 ^ 3 + b * 19 ^ 2 + c * 19 + d = 1 := h1
  have eq2 : a * 62 ^ 3 + b * 62 ^ 2 + c * 62 + d = 2 := h2
  have h3 : a * (62^3 - 19^3) + b * (62^2 - 19^2) + c * (62 - 19) = 1 := by 
    linarith
  have h4 : (62 : ℤ) - 19 = 43 := by norm_num
  have h5 : (62^2 - 19^2 : ℤ) = 43 * (62 + 19) := by ring
  have h6 : (62^3 - 19^3 : ℤ) = 43 * (62^2 + 62 * 19 + 19^2) := by ring
  rw [h6, h5, h4] at h3
  have h7 : 43 * (a * (62^2 + 62 * 19 + 19^2) + b * (62 + 19) + c) = 1 := by 
    linarith
  omega