import Mathlib

theorem algebra_313988 {a : ℕ → ℝ} (ha : a 1 = 4)
    (hsum : ∀ n, ∑ i in Finset.range (n + 1), a i - 3 * ∑ i in Finset.range n, a i - 2 * n - 4 = 0) :
    (∀ n, a n = 2 ^ n - 1) ∧
    (∀ n, ∑ i in Finset.range (n + 1), a i * (n + 1 - i) = (5 * 3 ^ (n + 1) - 15) / 4 - n * (n + 6) / 2) := by
  have h1 := hsum 0
  simp [Finset.sum_range_succ] at h1
  -- contradiction found
  -- Lean is to prove a goals which contradicts facts
  have h2 := hsum 1
  simp [Finset.sum_range_succ, ha] at h2
  all_goals
    linarith