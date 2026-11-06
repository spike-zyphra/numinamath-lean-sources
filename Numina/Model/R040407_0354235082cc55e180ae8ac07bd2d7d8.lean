import Mathlib
theorem algebra_313892 {a : ℕ → ℕ → ℝ} (ha : ∀ i j, i ≥ j → a i j = a 0 0 + (i - 1) * (1 / 2) ^ j)
    (n : ℕ) : a n 3 = n / 16 := by
  have h1 := ha 0 0 (by norm_num)
  norm_num at h1 
  all_goals linarith