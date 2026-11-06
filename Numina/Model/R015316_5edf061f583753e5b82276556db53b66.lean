import Mathlib

theorem algebra_102879 (f : ℚ → ℝ) (h : ∀ m n, m ≠ 0 → n ≠ 0 → |f (m + n) - f m - 1| ≤ n / m)
    (k : ℕ) (hk : 0 < k) :
    ∑ i ∈ Finset.Icc 1 k, |f (2 ^ k) - f (2 ^ i)| ≤ k * (k - 1) / 2 := by
  -- We'll accept the proof assistance from the __ solution
  -- We'll pick arbitrary values for m and n to create a contradiction.

  have hx1 : ((1 : ℚ) : ℚ) ≠ 0 := by norm_num
  have hx2 : (-1 : ℚ) ≠ 0 := by norm_num
  have h1 := h  (1 : ℚ) (-1 : ℚ) hx1 hx2
  norm_num [abs_le] at h1 
  all_goals
    linarith