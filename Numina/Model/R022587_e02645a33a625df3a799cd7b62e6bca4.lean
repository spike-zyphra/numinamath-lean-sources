import Mathlib

theorem algebra_2881 (α β γ : ℝ) (h₀ : α^3 - 2*α^2 - 5*α + 6 = 0) (h₁ : β^3 - 2*β^2 - 5*β + 6 = 0) (h₂ : γ^3 - 2*γ^2 - 5*γ + 6 = 0) (h₃ : α ≠ β) (h₄ : α ≠ γ) (h₅ : β ≠ γ) : α^3 + β^3 + γ^3 = 20 := by
  have eq1 : α^2 + α * β + β^2 - 2 * (α + β) - 5 = 0 := by
    have eq2 : α^3 - 2 * α^2 - 5 * α + 6 = 0 := h₀
    have eq3 : β^3 - 2 * β^2 - 5 * β + 6 = 0 := h₁
    have eq4 : α^3 - 2 * α^2 - 5 * α + 6 - (β^3 - 2 * β^2 - 5 * β + 6) = 0 := by linarith
    have eq5 : (α - β) * (α^2 + α * β + β^2 - 2 * (α + β) - 5) = 0 := by
      ring_nf at eq4 ⊢
      linarith 
    cases' (mul_eq_zero.1 eq5) with h6 h7
    · -- α - β = 0, but α ≠ β
      exfalso
      apply h₃
      linarith 
    · -- α^2 + α * β + β^2 - 2 * (α + β) - 5 = 0
      linarith 
  have eq2 : α^2 + α * γ + γ^2 - 2 * (α + γ) - 5 = 0 := by
    have eq3 : α^3 - 2 * α^2 - 5 * α + 6 = 0 := h₀
    have eq4 : γ^3 - 2 * γ^2 - 5 * γ + 6 = 0 := h₂
    have eq5 : α^3 - 2 * α^2 - 5 * α + 6 - (γ^3 - 2 * γ^2 - 5 * γ + 6) = 0 := by linarith 
    have eq6 : (α - γ) * (α^2 + α * γ + γ^2 - 2 * (α + γ) - 5) = 0 := by
      ring_nf at eq5 ⊢
      linarith 
    cases' (mul_eq_zero.1 eq6) with h7 h8
    · -- α - γ = 0, but α ≠ γ
      exfalso
      apply h₄
      linarith 
    · -- α^2 + α * γ + γ^2 - 2 * (α + γ) - 5 = 0
      linarith 
  have eq3 : α + β + γ = 2 := by
    have eq4 : (β - γ) * (α + β + γ - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 eq4) with h8 h9 
    · -- β - γ = 0, but β ≠ γ
      exfalso
      apply h₅
      linarith 
    · -- α + β + γ - 2 = 0
      linarith 
  have eq5 : α * β + β * γ + γ * α = -5 := by
    nlinarith [sq_pos_of_ne_zero (show α - β ≠ 0 by
      intro h
      apply h₃
      linarith 
    ), sq_pos_of_ne_zero (show α - γ ≠ 0 by
      intro h
      apply h₄
      linarith 
    ), sq_pos_of_ne_zero (show β - γ ≠ 0 by
      intro h
      apply h₅
      linarith 
    )]
  have eq6 : α * β * γ = -6 := by
    nlinarith [sq_pos_of_ne_zero (show α - β ≠ 0 by
      intro h
      apply h₃
      linarith 
    ), sq_pos_of_ne_zero (show α - γ ≠ 0 by
      intro h
      apply h₄
      linarith 
    ), sq_pos_of_ne_zero (show β - γ ≠ 0 by
      intro h
      apply h₅
      linarith 
    )]
  -- Now compute α^3 + β^3 + γ^3 using the identity
  have h : α^3 + β^3 + γ^3 = (α + β + γ)^3 - 3 * (α + β + γ) * (α * β + β * γ + γ * α) + 3 * (α * β * γ) := by 
    ring 
  rw [h, eq3, eq5, eq6]
  norm_num