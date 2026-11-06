import Mathlib

theorem algebra_177611 (a : ℕ → ℤ) (ha1 : a 1 = 2)
    (han : ∀ n ≥ 1, a (n + 1) = a n + 2 * n) : a 100 = 9902 := by
  norm_num [ha1, han] at *
  <;> omega