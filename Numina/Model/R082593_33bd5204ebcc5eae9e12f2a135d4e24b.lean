import Mathlib

theorem algebra_564 (a : ℕ → ℤ) (ha0 : a 0 = 0) (ha1 : a 1 = 1) (ha3 : a 2 = 3)
    (ha8 : a 3 = 8) (ha21 : a 4 = 21) (ha : ∀ i, i > 4 → a i = 3 * a (i - 1) - a (i - 2)) :
    a 69 % 6 = 4 := by
  norm_num [ha0, ha1, ha3, ha8, ha21, ha] at *
  <;> omega