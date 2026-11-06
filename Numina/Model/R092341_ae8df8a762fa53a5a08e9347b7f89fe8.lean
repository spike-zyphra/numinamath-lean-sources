import Mathlib

theorem algebra_258530 (m : ℕ) (h : 3 ^ m = 81) : m ^ 3 = 64 := by
  have h1 : m = 4 := by
    exact Nat.pow_right_injective (by norm_num) h
  calc
    m ^ 3 = 4 ^ 3 := by rw [h1]
    _ = 64 := by norm_num