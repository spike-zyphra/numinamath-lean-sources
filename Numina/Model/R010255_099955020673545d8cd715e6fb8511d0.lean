import Mathlib


theorem number_theory_13327 {a : ℕ → ℕ} (ha : ∀ n, a n = 6^n + 8^n): a 83 % 49 = 35 := by
  rw [ha 83]
  norm_num