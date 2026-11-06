import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_203296 {a b : ℝ} (ha : a^2 + b^2 = 1) (hb : arcsin a = arccos b)
  (h : ∀ x y, x^2 + y^2 ≤ 2 / sqrt 3 → a * x^2 + b * y^2 ≥ 1) :
  π / 6 ≤ arcsin b ∧ arcsin b < π / 4 ∨ π / 4 < arcsin b ∧ arcsin b ≤ π / 3 := by
  have h1 := h (0 : ℝ) (0 : ℝ) (by
    have h2 : (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 ≤ 2 / sqrt 3 := by
      have h3 : (0 : ℝ) ^ 2 = (0 : ℝ) := by
        norm_num
      have h4 : (0 : ℝ) ^ 2 = (0 : ℝ) := by
        norm_num
      have h5 : sqrt 3 > 0 := by
        positivity
      have h6 : (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = (0 : ℝ) := by
        norm_num
      rw [h6]
      have h7 : (0 : ℝ) ≤ 2 / sqrt 3 := by
        have h8 : sqrt 3 > 0 := by
          positivity
        apply (le_div_iff₀ h8).mpr
        all_goals
          nlinarith
      linarith [h7]
    linarith
  )
  have h2 : a * (0: ℝ) ^ 2 + b * (0: ℝ) ^ 2 = (0: ℝ) := by
    norm_num
  have h3 : a * (0: ℝ) ^ 2 + b * (0: ℝ) ^ 2 ≥ 1 := by
    linarith [h1]
  nlinarith