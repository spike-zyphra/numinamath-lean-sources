import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_194698 (a b : ℝ) (h₀ : a^2 + b^2 = 1) (h₁ : arcsin a = arccos b)
  (h₂ : ∀ x y, x^2 + y^2 ≤ 2 / sqrt 3 → a * x^2 + b * y^2 ≥ 1) :
  π / 6 ≤ arccos a ∧ arccos a ≤ π / 3 := by

  have h3 := h₂ 0 0 (by
    have h4 : (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 ≤ 2 / sqrt 3 := by
      norm_num
      have h5 : (0 : ℝ) ≤ (2 / sqrt 3 : ℝ) := by positivity
      linarith
    linarith
  )
  norm_num at h3
  all_goals linarith