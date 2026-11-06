import Mathlib

open Real

theorem inequalities_271591 (α β γ : ℝ) (h₀ : 0 < α) (h₁ : α < β) (h₂ : β < γ) :
    0 < 8 / π^2 * (γ - β) / (β - α) := by
  have h3 : 0 < π := Real.pi_pos
  have h4 : 0 < π ^ 2 := by
    nlinarith [h3]
  have h5 : 0 < γ - β := by linarith
  have h6 : 0 < β - α := by linarith
  have h7 : 0 < (8 / π ^ 2 : ℝ) := by
    positivity
  have h8 : 0 < (γ - β) / (β - α) := by
    apply div_pos
    linarith
    linarith
  have h9 : 0 < 8 / π^2 * (γ - β) / (β - α) := by
    positivity
  exact h9