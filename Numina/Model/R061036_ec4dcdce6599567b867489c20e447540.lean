import Mathlib

theorem algebra_226293 (α β : ℝ) (h₀ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₁ : β ∈ Set.Ioo (-Real.pi / 2) 0)
    (h₂ : Real.sin β = -5 / 13) (h₃ : Real.sqrt ((Real.cos α - Real.cos β)^2 + (Real.sin α - Real.sin β)^2) = 2 * Real.sqrt 5 / 5) :
    Real.sin α = 33 / 65 := by
  have h5 : Real.sqrt ((Real.cos α - Real.cos β)^2 + (Real.sin α - Real.sin β)^2) ^ 2 = (2 * Real.sqrt 5 / 5) ^ 2 := by
    rw [h₃]
  have h6 : Real.sqrt ((Real.cos α - Real.cos β)^2 + (Real.sin α - Real.sin β)^2) ^ 2 = (Real.cos α - Real.cos β) ^ 2 + (Real.sin α - Real.sin β) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h7 : (2 * Real.sqrt 5 / 5) ^ 2 = 4 / 5 := by
    calc
      (2 * Real.sqrt 5 / 5) ^ 2 = 4 * (Real.sqrt 5) ^ 2 / 25 := by ring_nf
      _ = 4 * 5 / 25 := by rw [Real.sq_sqrt (by norm_num)]
      _ = 20 / 25 := by norm_num
      _ = 4 / 5 := by norm_num
  rw [h6, h7] at h5
  have h8 : (Real.cos α - Real.cos β) ^ 2 + (Real.sin α - Real.sin β) ^ 2 = 4 / 5 := by
    linarith
  
  have h9 : Real.cos β > 0 := by
    have h9a : -Real.pi / 2 < β := h₁.left
    have h9b : β < 0 := h₁.right
    have h9c : Real.cos β > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [h9a, Real.pi_pos]
      · linarith [h9b, Real.pi_pos]
    exact h9c
  
  have h10 : Real.cos β = 12 / 13 := by
    have h10a : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
    rw [h₂] at h10a
    have h10b : Real.cos β ^ 2 = 144 / 169 := by nlinarith [h10a]
    have h10c : Real.cos β = 12 / 13 := by
      nlinarith [h10b, h9]
    exact h10c
  
  rw [h10, h₂] at h8
  
  have h11 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  
  have h9a : 0 < α := h₀.left
  have h9b : α < Real.pi / 2 := h₀.right
  have h9c : Real.sin α > 0 := by
      apply Real.sin_pos_of_pos_of_lt_pi
      linarith [h9a, Real.pi_pos]
      linarith [h9b, Real.pi_pos]

  have h12 : Real.sin α = 33 / 65 := by
    nlinarith [h8, h11, h9c, sq_nonneg (Real.sin α - 33 / 65), sq_nonneg (Real.cos α - 56 / 65)]
  
  exact h12