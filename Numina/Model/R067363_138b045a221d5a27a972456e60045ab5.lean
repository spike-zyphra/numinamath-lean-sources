import Mathlib

theorem algebra_7124 (a : ℕ → ℕ) (ha0 : a 0 = 3)
    (han : ∀ n, a (n + 1) = 2 * a n + 1) :
    a 9 = 2047 := by 
  norm_num [ha0, han]