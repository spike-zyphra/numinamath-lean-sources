import Mathlib

theorem algebra_347662 (α : ℝ) (h₀ : Real.sin α = 4 / 5) (h₁ : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos (α / 2) = 2 * √5 / 5 := by
  rcases h₁ with ⟨h₂, h₃⟩
  have h4 : Real.cos α > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [h₂, Real.pi_pos]
    · linarith [h₃, Real.pi_pos]
  have h5 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  rw [h₀] at h5
  have h6 : Real.cos α = 3 / 5 := by
    nlinarith [h4]
  have h7 : Real.cos (α / 2) ^ 2 = (1 + Real.cos α) / 2 := by
    have h8 : Real.cos (α / 2) ^ 2 = (1 + Real.cos α) / 2 := by
      have h9 : Real.cos (α / 2) ^ 2 = (1 + Real.cos α) / 2 := by
        rw [Real.cos_sq]
        ring_nf
        <;> simp [Real.sin_sq]
        <;> linarith
      linarith
    linarith
  rw [h6] at h7
  have h8 : 0 < α / 2 := by
    linarith
  have h9 : α / 2 < Real.pi / 2 := by
    linarith [h₃, Real.pi_pos]
  have h10 : Real.cos (α / 2) > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [h8, Real.pi_pos]
    · linarith [h9, Real.pi_pos]
  have h11 : Real.cos (α / 2) ^ 2 = 4 / 5 := by
    linarith
  have h12 : Real.cos (α / 2) = Real.sqrt (4 / 5) := by
    have h13 : Real.cos (α / 2) > 0 := h10
    have h14 : Real.cos (α / 2) ^ 2 = 4 / 5 := h11
    have h15 : Real.cos (α / 2) = Real.sqrt (4 / 5) := by
      rw [←h14]
      field_simp [h13]
    exact h15
  have h13 : Real.sqrt (4 / 5) = 2 * Real.sqrt 5 / 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h13] at h12
  linarith [h12, Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]