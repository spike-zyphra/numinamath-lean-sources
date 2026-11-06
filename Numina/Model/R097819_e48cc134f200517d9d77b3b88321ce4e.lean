import Mathlib

theorem algebra_322806 (α β : ℝ) (h₀ : α ∈ Set.Ioo (-2 * Real.pi) (-Real.pi)) (h₁ : β ∈ Set.Ioo (-2 * Real.pi) (-Real.pi))
    (h₂ : α < β) :
    2 * α - β ∈ Set.Ioo (-3 * Real.pi) (-Real.pi) := by
  rcases h₀ with ⟨h01, h02⟩
  rcases h₁ with ⟨h11, h12⟩
  constructor
  · -- Prove $-3\pi < 2\alpha - \beta$
    nlinarith [Real.pi_pos, Real.pi_gt_three]
  · -- Prove $2\alpha - \beta < -\pi$
    nlinarith [Real.pi_pos, Real.pi_gt_three]