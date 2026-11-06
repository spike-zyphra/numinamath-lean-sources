import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_80483 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = min (min (4 * x + 1) (x + 2)) (-2 * x + 4)) :
  IsGreatest (range f) (8 / 3) := by
    constructor
    · -- First, we'll show that $8/3$ is achievable at $x = 2/3$
      use 2 / 3
      norm_num [h₀]
    · -- Now, we need to prove that for any $y \in \operatorname{range}(f)$, $y \leq 8/3$
      intro y
      rintro ⟨x, hx⟩
      rw [h₀] at hx
      by_cases h1 : 4 * x + 1 ≤ x + 2
      · -- Case 1: $4x + 1 \leq x + 2$
        rw [min_eq_left h1] at hx
        by_cases h2 : 4 * x + 1 ≤ -2 * x + 4
        · -- Case 1a: $4x + 1 \leq -2x + 4$
          rw [min_eq_left h2] at hx
          linarith
        · -- Case 1b: $-2x + 4 < 4x + 1$
          rw [min_eq_right (le_of_not_ge h2)] at hx
          linarith
      · -- Case 2: $x + 2 < 4x + 1$
        rw [min_eq_right (le_of_not_ge h1)] at hx
        by_cases h2 : x + 2 ≤ -2 * x + 4
        · -- Case 2a: $x + 2 \leq -2x + 4$
          rw [min_eq_left h2] at hx
          linarith
        · -- Case 2b: $-2x + 4 < x + 2$
          rw [min_eq_right (le_of_not_ge h2)] at hx
          linarith