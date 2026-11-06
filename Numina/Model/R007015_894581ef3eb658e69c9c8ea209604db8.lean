import Mathlib

theorem algebra_22001 {b : ℝ} (hb : b > 0) (h : ∀ x, x^2 + b * x + 1 = (x + m)^2 - 63) :
    b = 16 := by 
  have eq0 := h 0
  have eq1 := h 1
  have eq_1 := h (-1)
  have h1 : m^2 = 64 := by
    nlinarith [eq0]
  have h2 : m = 8 ∨ m = -8 := by
    have h3 : m^2 - 64 = 0 := by linarith
    have h4 : (m - 8) * (m + 8) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h4) with
    | inl h5 => 
      left 
      linarith 
    | inr h6 => 
      right 
      linarith 
  cases h2 with 
  | inl hm8 => 
    have eq1' := eq1
    rw [hm8] at eq1'
    nlinarith
  | inr hm_8 => 
    have eq1' := eq1
    rw [hm_8] at eq1'
    nlinarith