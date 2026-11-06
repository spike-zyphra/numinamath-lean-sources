import Mathlib

open Real Set

theorem algebra_12851 {f : ℝ → ℝ}
    (hf : ∀ x, f x = min (min (x + 2) (4 * x + 1)) (-2 * x + 4)) :
    IsGreatest (range f) (8 / 3) := by 
  constructor
  · -- We need to prove that 8/3 is in the range of f
    use 2 / 3
    rw [hf]
    norm_num [min_eq_left, min_eq_right]
    all_goals norm_num 
  · -- Now we need to prove that 8/3 is the greatest
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx
    by_cases h1 : (x + 2) ≤ (4 * x + 1)
    · -- Case where $x + 2 \leq 4 * x + 1$
      rw [min_eq_left h1] at hx
      by_cases h2 : (x + 2) ≤ (-2 * x + 4)
      · -- Case where $x + 2 \leq -2 * x + 4$
        rw [min_eq_left h2] at hx
        linarith
      · -- Case where $x + 2 > -2 * x + 4$
        rw [min_eq_right (le_of_not_le h2)] at hx
        linarith
    · -- Case where $x + 2 > 4 * x + 1$
      rw [min_eq_right (le_of_not_le h1)] at hx
      by_cases h2 : (4 * x + 1) ≤ (-2 * x + 4)
      · -- Case where $4 * x + 1 \leq -2 * x + 4$
        rw [min_eq_left h2] at hx
        linarith
      · -- Case where $4 * x + 1 > -2 * x + 4$
        rw [min_eq_right (le_of_not_le h2)] at hx
        linarith