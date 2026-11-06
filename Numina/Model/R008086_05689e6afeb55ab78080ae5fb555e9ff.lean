import Mathlib

theorem algebra_19122 : IsLeast {n : ℤ | ∃ x, n = x^2 - 6 * x + 13} 4 := by
  constructor
  · -- First part: show 4 is in the set by using x = 3
    use 3
    norm_num
  · -- Second part: show any element in the set is ≥ 4
    intro n hn
    rcases hn with ⟨x, hx⟩
    have h : x^2 - 6 * x + 13 ≥ 4 := by
      nlinarith [sq_nonneg (x - 3 : ℤ)]
    linarith [hx, h]