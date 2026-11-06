import Mathlib

theorem algebra_96302 {b c : ℝ} (h : (2^2+b*2+c=3 ∧ 4^2+b*4+c=3)) : c=11 := by
  rcases h with ⟨h₁, h₂⟩
  linarith