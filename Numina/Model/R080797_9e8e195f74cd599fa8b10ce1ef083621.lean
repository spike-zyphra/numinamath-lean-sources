import Mathlib

theorem algebra_1836 (h : (16 : ℝ) * (1 + 0.8 + 0.8 ^ 2 + 0.8 ^ 3) = 144) :
  ∀ x, (16 : ℝ) * (1 + 0.8 + 0.8 ^ 2 + 0.8 ^ 3 + ∑ i ∈ Finset.range x, 0.8 ^ (i + 1)) = 144 - 128 * (4 / 5) ^ x := by
  have h1 : False := by
    norm_num at h
    all_goals linarith
  intro x
  exfalso
  exact h1