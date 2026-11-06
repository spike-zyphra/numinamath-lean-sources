import Mathlib

open Real

theorem inequalities_52457 (a : ℕ → ℝ)
    (h₀ : a 1 = 0)
    (h₁ : ∀ n, a (n + 1) = (∑ i in Finset.Icc 1 n, a i) / n + 1) :
    a 2016 > 1 / 2 + a 1000 := by
  have h2 := h₁ 0
  norm_num [Finset.sum_eq_zero] at h2 h₀ 
  all_goals linarith