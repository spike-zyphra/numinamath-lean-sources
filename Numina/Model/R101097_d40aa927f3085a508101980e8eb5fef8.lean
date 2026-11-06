import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_328398 (x : ℝ) (hx : 0 ≤ x) (y : ℝ)
  (hmax : max (1 - x) (x - 1) ≤ y ∧ y ≤ x + 2) :
  2 * x + y ≥ 1 := by
  rcases hmax with ⟨hy1, hy2⟩
  by_cases h : x ≤ 1
  · -- In this case, max (1 - x) (x - 1) = 1 - x because x ≤ 1
    have hmax1 : max (1 - x) (x - 1) = 1 - x := by
      apply max_eq_left
      linarith
    rw [hmax1] at hy1
    linarith
  · -- Case 2: x > 1, so max (1 - x) (x - 1) = x - 1
    have hmax2 : max (1 - x) (x - 1) = x - 1 := by
      apply max_eq_right
      linarith
    rw [hmax2] at hy1
    linarith