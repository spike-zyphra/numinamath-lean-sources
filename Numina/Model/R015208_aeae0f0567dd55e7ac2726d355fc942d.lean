import Mathlib

theorem algebra_22095 {m n : ℤ} (h₀ : 3 * m + 4 * n = 47) (h₁ : m + n = 15) :
    m = 13 := by
  have h2 : n = 15 - m := by 
    linarith
  rw [h2] at h₀
  linarith