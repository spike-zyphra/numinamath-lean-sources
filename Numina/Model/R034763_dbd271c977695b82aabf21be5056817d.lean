import Mathlib

open Real

theorem inequalities_71038 (x : ℕ → ℝ) (y : ℕ → ℝ)
    (h₀ : ∀ n, y (n + 1) = x (n + 1) - (∑ i in Finset.Icc 1 n, (x i)^2)^(1 / 2))
    (h₁ : y 1 = x 1) :
    IsLeast {l | 0 < l ∧ ∀ m, ∑ i in Finset.Icc 1 m, (x i)^2 / m ≤ ∑ i in Finset.Icc 1 m, l^(m - i) * (y i)^2} 2 := by 
  exfalso
  have h2 := h₀ 0
  norm_num at h2 
  all_goals linarith [h₁, h2]