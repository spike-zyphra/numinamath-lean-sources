import Mathlib

theorem algebra_118393 (α β : ℝ) (h₁ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₂ : β ∈ Set.Ioo 0 (Real.pi / 2))
    (h₃ : Real.cos α = 4 / 5) (h₄ : Real.tan (α - β) = -1 / 3) :
    Real.cos β = 9 * Real.sqrt 10 / 50 := by
  rcases h₁ with ⟨h₁₀, h₁₁⟩
  rcases h₂ with ⟨h₂₀, h₂₁⟩
  have h₅ : Real.sin α = 3 / 5 := by
    have h₆ : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    rw [h₃] at h₆
    have h₇ : Real.sin α ^ 2 = 9 / 25 := by linarith
    have h₈ : 0 < Real.sin α := by 
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith [h₁₀, Real.pi_pos]
      · linarith [h₁₁, Real.pi_pos]
    nlinarith
  have h₇ : Real.sin α = 3 / 5 := h₅
  have h₈ : Real.cos (α - β) ≠ 0 := by
    by_contra h
    have htan : Real.tan (α - β) = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h]
    linarith [htan, h₄]
  have htan : Real.sin (α - β) / Real.cos (α - β) = -1 / 3 := by
    rw [Real.tan_eq_sin_div_cos] at h₄
    linarith
  have h9 : Real.sin (α - β) = -1 / 3 * Real.cos (α - β) := by
    have hcos : Real.cos (α - β) ≠ 0 := h₈
    field_simp [hcos] at htan ⊢
    linarith
  have h10 : Real.sin (α - β) = Real.sin α * Real.cos β - Real.cos α * Real.sin β := by
    rw [Real.sin_sub]
  have h11 : Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β := by
    rw [Real.cos_sub]
  rw [h10, h11, h₃, h₅] at h9
  -- We have 13 * cos β = 9 * sin β
  have h13 : 13 * Real.cos β = 9 * Real.sin β := by
    nlinarith
  have h14 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
  have h16 : Real.sin β = 13 / 9 * Real.cos β := by
    linarith [h13]
  rw [h16] at h14
  have h17 : Real.cos β ^ 2 = 81 / 250 := by
    nlinarith
  have h18 : Real.cos β > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [h₂₀, Real.pi_pos]
    · linarith [h₂₁, Real.pi_pos]
  -- Now we take the sqrt to find cos β
  have h19 : Real.cos β = Real.sqrt (81 / 250) := by
    have h20 : Real.cos β ^ 2 = 81 / 250 := h17
    have h21 : Real.cos β ≥ 0 := by linarith [h18]
    have h22 : Real.sqrt (Real.cos β ^ 2) = Real.sqrt (81 / 250) := by
      rw [h20]
    have h23 : Real.sqrt (Real.cos β ^ 2) = Real.cos β := by
      rw [Real.sqrt_sq (show 0 ≤ Real.cos β by linarith)]
    linarith [h23, h22]
  have h24 : Real.sqrt (81 / 250) = 9 * Real.sqrt 10 / 50 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  rw [h19, h24]