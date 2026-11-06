import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_131093 {f : ℝ → ℝ}
  (hf : ∀ x, f x = min (min (2 * x) (x + 1)) (10 - 2 * x)) :
  IsGreatest (range f) 4 := by
  constructor
  · -- We prove that 4 belongs to the range of f
    use 3
    norm_num [hf]
  · -- We prove that 4 is greatest in the range of f
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf x] at hx
    by_cases h1 : 2 * x ≤ x + 1
    · -- In this case, min (2 * x) (x + 1) = 2 * x
      rw [min_eq_left h1] at hx
      by_cases h2 : 2 * x ≤ 10 - 2 * x
      · -- In this case, min (2 * x) (10 - 2 * x) = 2 * x
        rw [min_eq_left h2] at hx
        linarith
      · -- In this case, min (2 * x) (10 - 2 * x) = 10 - 2 * x
        rw [min_eq_right (le_of_not_le h2)] at hx
        linarith
    · -- In this case, min (2 * x) (x + 1) = x + 1
      rw [min_eq_right (le_of_not_le h1)] at hx
      by_cases h2 : x + 1 ≤ 10 - 2 * x
      · -- In this case, min (x + 1) (10 - 2 * x) = x + 1
        rw [min_eq_left h2] at hx
        linarith
      · -- In this case, min (x + 1) (10 - 2 * x) = 10 - 2 * x
        rw [min_eq_right (le_of_not_le h2)] at hx
        linarith