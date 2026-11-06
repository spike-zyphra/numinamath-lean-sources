import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_185876 (x : ℝ) (h : ∀ m ∈ Icc (1/2) 3, x^2 + m * x + 4 > 2 * m + 4 * x) :
    x > 2 ∨ x < -1 := by
  have h1 := h (1/2) (by norm_num)
  have h2 := h 3 (by norm_num)
  by_cases h3 : x > 2
  · -- If x > 2, we're done
    left
    exact h3
  · -- If not x > 2, let's prove x < -1
    have h4 : x ≤ 2 := by linarith
    have h5 : x^2 + (1/2 : ℝ) * x + 4 > 2 * (1/2 : ℝ) + 4 * x := by linarith [h1]
    have h6 : x^2 + (3 : ℝ) * x + 4 > 2 * (3 : ℝ) + 4 * x := by linarith [h2]
    have h7 : x < -1 := by
      nlinarith
    right
    exact h7