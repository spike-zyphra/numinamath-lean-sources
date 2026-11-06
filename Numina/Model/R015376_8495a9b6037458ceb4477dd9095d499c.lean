import Mathlib

theorem inequalities_170730 (f : ℚ → ℝ) (h : ∀ m n, m ≠ 0 → n ≠ 0 → |f (m + n) - f m| ≤ m / n)
    (k : ℕ) (hk : 0 < k) :
    ∑ i ∈ Finset.Icc 1 k, |f (2 ^ k) - f (2 ^ i)| ≤ k * (k - 1) / 2 := by
  have h2 : (1 : ℚ) ≠ 0 := by norm_num
  have h3 : (-1 : ℚ) ≠ 0 := by norm_num
  specialize h (1 : ℚ) (-1 : ℚ) h2 h3
  norm_num at h
  all_goals linarith [abs_nonneg (f (0 : ℚ) - f (1 : ℚ)), abs_nonneg (f (0 : ℚ) - f (1 : ℚ))]