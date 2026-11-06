import Mathlib

theorem number_theory_321506 (a : ℕ → ℤ) (ha : ∀ n, a n = 6 ^ n + 8 ^ n) :
    a 2018 % 49 = 2 := by
  rw [ha 2018]
  norm_num