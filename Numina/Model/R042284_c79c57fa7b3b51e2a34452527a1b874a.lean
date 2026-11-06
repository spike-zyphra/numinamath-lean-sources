import Mathlib

open Real Set
open scoped Real

theorem algebra_266129 :
    IsGreatest {x : ℝ | ∃ α β : ℝ, α ∈ Ioo 0 (π/2) ∧ β ∈ Ioo 0 (π/2) ∧ sin β = 2 * cos (α + β) * sin α ∧ α + β ≠ π/2 ∧ x = tan β} (sqrt 3 / 3) := by
  constructor
  · -- Show that sqrt(3)/3 is in the set
    use Real.pi / 6, Real.pi / 6
    constructor
    · -- Show α ∈ (0, π/2)
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    constructor
    · -- Show β ∈ (0, π/2)
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    constructor
    · -- Show sin β = 2 * cos (α + β) * sin α
      have h1 : sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
      have h4 : cos (Real.pi / 6 + Real.pi / 6) = 1 / 2 := by
        have h5 : Real.pi / 6 + Real.pi / 6 = Real.pi / 3 := by ring_nf
        rw [h5]
        exact Real.cos_pi_div_three
      rw [h4, h1]
      linarith
    constructor
    · -- Show α + β ≠ π/2
      have h5 : Real.pi / 6 + Real.pi / 6 = Real.pi / 3 := by ring_nf
      rw [h5]
      have h6 : Real.pi / 3 ≠ Real.pi / 2 := by
        linarith [Real.pi_pos]
      exact h6
    · -- Show x = tan β
      have h7 : tan (Real.pi / 6) = Real.sqrt 3 / 3 := by
        rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_six, Real.cos_pi_div_six]
        field_simp
        <;> ring_nf <;> norm_num
      linarith [h7]
  · -- Show that sqrt(3)/3 is greatest in the set
    intro x hx
    rcases hx with ⟨α, β, hα, hβ, heq1, hne, hx⟩
    have h1 : 0 < α := hα.1
    have h2 : α < Real.pi / 2 := hα.2
    have h3 : 0 < β := hβ.1
    have h4 : β < Real.pi / 2 := hβ.2
    have h5 : sin α > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have h6 : cos α > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have h7 : sin β > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have h8 : cos β > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have heq2 : sin β = 2 * (cos α * cos β - sin α * sin β) * sin α := by
      have h9 : cos (α + β) = cos α * cos β - sin α * sin β := by
        rw [cos_add]
      rw [h9] at heq1
      linarith
    have heq3 : tan β = (2 * cos α * sin α) / (1 + 2 * sin α ^ 2) := by
      have heq4 : sin β * (1 + 2 * sin α ^ 2) = 2 * cos α * sin α * cos β := by
        nlinarith [heq2]
      have hcos : cos β > 0 := h8
      have heq5 : tan β * (1 + 2 * sin α ^ 2) = 2 * cos α * sin α := by
        have heq6 : tan β = sin β / cos β := by
          rw [tan_eq_sin_div_cos]
        rw [heq6]
        have heq7 : sin β / cos β * (1 + 2 * sin α ^ 2) = 2 * cos α * sin α := by
          field_simp [hcos] at *
          nlinarith [heq4]
        linarith [heq7]
      field_simp at heq5 ⊢
      linarith
    rw [heq3] at hx
    have h11 : (2 * cos α * sin α) / (1 + 2 * sin α ^ 2) ≤ Real.sqrt 3 / 3 := by
      have h12 : 0 < (1 + 2 * sin α ^ 2 : ℝ) := by
        nlinarith [sq_nonneg (sin α), Real.sin_sq_add_cos_sq α]
      apply (div_le_div_iff (by nlinarith) (by nlinarith)).mpr
      nlinarith [sq_nonneg (cos α - Real.sqrt 3 / 2), sq_nonneg (sin α - 1 / 2), 
          sq_nonneg (cos α - Real.sqrt 3 * sin α), sq_nonneg (cos α - (1 / 2) * Real.sqrt 3), 
          sq_nonneg (sin α - 1 / 2), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), 
          Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), 
          Real.sin_sq_add_cos_sq α, 
          mul_pos h5 h6, 
          mul_pos h6 h7, 
          mul_pos h5 h7
        ]
    linarith [h11, hx]