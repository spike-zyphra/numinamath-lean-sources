import Mathlib

theorem algebra_9720
  (a : ℕ → ℝ)
  (h₀ : a 0 = 20)
  (h₁ : a 1 = 23)
  (h₂ : ∀ n, a (n + 2) = a (n + 1) - a n) :
  (∑ i in Finset.range 20, a i) / 20 = 2.15 := by
  simp [Finset.sum_range_succ, h₀, h₁, h₂]
  norm_num