import Mathlib

theorem algebra_309255 (a b c : ℝ) (h₀ : a - 7 * b + 8 * c = 4) (h₁ : 8 * a + 4 * b - c = 7) :
    a^2 - b^2 + c^2 = 1 := by 
  have eq2 : a = 7 * b - 8 * c + 4 := by linarith [h₀]
  rw [eq2] at h₁ 
  have eq3 : 12 * b - 13 * c = -5 := by
    linarith
  have eq4 : b = (13 * c - 5) / 12 := by
    linarith
  have eq5 : a = (-5 * c + 13) / 12 := by
    rw [eq4] at eq2
    linarith
  rw [eq5, eq4]
  nlinarith [sq_nonneg ((-5 * c + 13) / 12), sq_nonneg ((13 * c - 5) / 12), sq_nonneg c, sq_nonneg ((-5 * c + 13) / 12 - (13 * c - 5) / 12), sq_nonneg ((-5 * c + 13) / 12 - c), sq_nonneg ((13 * c - 5) / 12 - c)]