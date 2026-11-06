import Mathlib

theorem algebra_13510 : IsLeast {n : ℝ | ∃ x, n = abs (x^2 - 16 * x + 55)} 0 := by 
  constructor
  · -- Let's verify x = 5 works
    use 5
    norm_num [abs_eq_zero]
  · -- Any n in the set is the absolute value.
    intro n hn
    rcases hn with ⟨x, hx⟩
    rw [hx]
    apply abs_nonneg