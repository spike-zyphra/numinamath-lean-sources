import Mathlib

theorem algebra_279989 (a b : ℝ) (h₁ : 1 ≤ a * (1 ^ 3 + 3 * 1) + b * (2 ^ 2 + 2 * 2 + 1) ∧ a * (1 ^ 3 + 3 * 1) + b * (2 ^ 2 + 2 * 2 + 1) ≤ 2)
    (h₂ : 2 ≤ a * (3 ^ 3 + 3 * 3) + b * (4 ^ 2 + 2 * 4 + 1) ∧ a * (3 ^ 3 + 3 * 3) + b * (4 ^ 2 + 2 * 4 + 1) ≤ 5) :
    3 / 2 ≤ a * (1 ^ 3 + 3 * 1) + b * (3 ^ 2 + 2 * 3 + 1) ∧ a * (1 ^ 3 + 3 * 1) + b * (3 ^ 2 + 2 * 3 + 1) ≤ 4 := by
  rcases h₁ with ⟨h11, h12⟩
  rcases h₂ with ⟨h21, h22⟩
  norm_num at h11 h12 h21 h22 ⊢
  constructor
  · linarith
  · linarith