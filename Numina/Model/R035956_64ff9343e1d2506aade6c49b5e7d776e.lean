import Mathlib

open BigOperators Complex Filter Finset Real TopologicalSpace Topology

theorem inequalities_325523 (f : ℚ → ℝ) (h : ∀ m n, |f (m + n) - f m| ≤ m / n)
    (k : ℕ) (hk : 0 < k) :
    ∑ i ∈ Finset.Icc 1 k, |f (2 ^ k) - f (2 ^ i)| ≤ (k * (k - 1)) / 2 := by 
  have h1 := h (1 : ℚ) (-1 : ℚ)
  norm_num at h1
  all_goals 
    linarith [abs_nonneg (f (0 : ℚ) - f (1 : ℚ))]