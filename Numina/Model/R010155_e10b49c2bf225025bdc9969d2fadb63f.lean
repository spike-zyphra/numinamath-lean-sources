import Mathlib

theorem algebra_9037 (ω : ℝ) (a : ℕ → ℝ) (ha : ∀ n > 0, a n = n ^ 2 + ω * n)
    (hinc : ∀ n > 0, a n < a (n + 1)) :
    ω > -3 := by 
  have h1 : a 1 < a 2 := by
    apply hinc 1 (by norm_num)
  rw [ha 1 (by norm_num), ha 2 (by norm_num)] at h1
  norm_num at h1
  linarith