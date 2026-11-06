import Mathlib

theorem number_theory_303927 {a : ℕ → ℤ} (ha : ∀ n, a n = 6 ^ n - 8 ^ n) :
    a 94 % 49 = 7 := by
  rw [ha]
  norm_num