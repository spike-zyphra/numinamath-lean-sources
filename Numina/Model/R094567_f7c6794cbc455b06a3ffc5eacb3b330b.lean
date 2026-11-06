import Mathlib

theorem algebra_290317 (a b c : ℝ) (h₀ : a + b + c = 425) (h₁ : 5 / 100 * a = 8 / 100 * b)
    (h₂ : 8 / 100 * b = 10 / 100 * c) :
    c = 100 := by
  have h3 : a = 16 / 10 * b := by
    linarith
  
  have h4 : b = 10 / 8 * c := by
    linarith
  
  have h5 : a = 2 * c := by
    rw [h4] at h3
    linarith
  
  rw [h5, h4] at h₀
  linarith