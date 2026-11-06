import Mathlib

theorem number_theory_188733 : ∑ d in (144 : ℕ).divisors, (1 : ℝ)/d = 403/144 := by
  have h1 : (144 : ℕ).divisors = {1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 36, 48, 72, 144} := by decide
  rw [h1]
  simp
  norm_num