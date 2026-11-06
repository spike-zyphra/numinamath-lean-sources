import Mathlib

theorem algebra_120247 (c m b : ℤ) (h₀ : c + 2*m + 3*b = 3*c + b) (h₁ : 3*c + b = 6*m) :
    2*c + 2*b = 5*m := by
  have eq4 : c = m + b := by
    linarith
  have eq5 : 4 * b = 3 * m := by
    rw [eq4] at h₁
    linarith
  linarith [eq4, eq5]