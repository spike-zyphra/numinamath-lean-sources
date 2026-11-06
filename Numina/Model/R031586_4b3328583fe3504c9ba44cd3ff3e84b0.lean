import Mathlib

theorem algebra_15576 : IsLeast {n : ℝ | ∃ x y, n = x ^ 2 + x * y + y ^ 2} 0 := by
  constructor
  · -- Show that 0 is in the set.
    use 0, 0
    all_goals norm_num
  · -- Show that 0 is the least element in the set.
    intro n hn
    rcases hn with ⟨x, y, h_eq⟩
    have h1 : x ^ 2 + x * y + y ^ 2 ≥ 0 := by 
      nlinarith [sq_nonneg (x + y / 2), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x), sq_nonneg (x + y / 2)]
    linarith [h_eq, h1]