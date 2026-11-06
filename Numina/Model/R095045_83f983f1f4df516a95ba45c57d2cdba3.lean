import Mathlib

theorem algebra_135917 (α β : ℝ) (h₀ : 0 < α ∧ α < Real.pi / 2) (h₁ : 0 < β ∧ β < Real.pi / 2)
    (h₂ : Real.cos α + Real.cos (2 * β) - Real.cos (α + β) = 3 / 2) :
    α = Real.pi / 3 ∧ β = Real.pi / 3 := by

  have h3 : Real.cos (2 * β) = 2 * Real.cos β ^ 2 - 1 := Real.cos_two_mul β
  have h4 : Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β := Real.cos_add α β
  rw [h3, h4] at h₂

  have hα1 : 0 < α := h₀.1
  have hα2 : α < Real.pi / 2 := h₀.2
  have hβ1 : 0 < β := h₁.1
  have hβ2 : β < Real.pi / 2 := h₁.2

  have h5 : Real.cos α > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]

  have h6 : Real.cos β > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]

  have h7 : Real.sin α > 0 := by 
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]

  have h8 : Real.sin β > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]

  nlinarith [Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β,
    Real.cos_sq_add_sin_sq (α + β), Real.cos_sq_add_sin_sq (2 * β),
    Real.cos_le_one (α), Real.cos_le_one (β), Real.cos_le_one (2 * β), Real.cos_le_one (α + β),
    Real.sin_le_one α, Real.sin_le_one β, Real.sin_le_one (α + β), Real.sin_le_one (2 * β),
    Real.pi_pos, hα1, hα2, hβ1, hβ2
  ]