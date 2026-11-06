import Mathlib

theorem algebra_13258 {a b : ℤ} (h₀ : a + b = 33) (h₁ : a^2 + b^2 = 725) :
    (a^(2022) + b^(2022)) % 2022 = 1055 := by 
  have h2 : a * b = 182 := by
    have h2 : a^2 + b^2 = (a + b)^2 - 2 * (a * b) := by 
      ring
    rw [h₀] at h2 
    linarith
  have h3 : a = 7 ∨ a = 26 := by
    have h4 : a^2 - 33 * a + 182 = 0 := by 
      have h5 : b = 33 - a := by linarith 
      rw [h5] at h₁ 
      nlinarith 
    have h6 : (a - 7) * (a - 26) = 0 := by
      nlinarith 
    cases (mul_eq_zero.1 h6) with
    | inl h7 =>
      left 
      linarith
    | inr h8 =>
      right 
      linarith
  cases h3 with
  | inl ha7 =>
    have hb26 : b = 26 := by 
      linarith 
    rw [ha7, hb26]
    norm_num 
  | inr ha26 =>
    have hb7 : b = 7 := by 
      linarith 
    rw [ha26, hb7]
    norm_num