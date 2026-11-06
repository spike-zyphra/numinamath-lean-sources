import Mathlib

theorem algebra_8193 {a : ℕ → ℤ} {d : ℤ} (ha : ∀ n, a n = a 0 + d * n) (hd : d = 11) (ha0 : a 0 = -1776) :
    |a 1979 - a 1976| = 33 := by
  have h1979 : a 1979 = a 0 + d * 1979 := ha 1979
  have h1976 : a 1976 = a 0 + d * 1976 := ha 1976
  rw [h1979, h1976, ha0, hd]
  norm_num [abs_of_nonneg]