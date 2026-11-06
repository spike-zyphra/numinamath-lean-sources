import Mathlib

theorem algebra_12529 {a : ℕ → ℝ} {r : ℝ} (ha : ∀ n, a n = a 0 * r ^ n)
    (hsum : ∀ n, ∑ i in Finset.range n, a i = ((a (n - 1) + 1) ^ 2) / 4) :
    ∑ i in Finset.range 20, a i = 0 := by 
  have h1 := hsum 0
  simp [Finset.sum_range_zero] at h1
  have h2 : a 0 = -1 := by 
    nlinarith
  have h3 := hsum 1 
  simp [Finset.sum_range_succ, h2] at h3
  all_goals nlinarith