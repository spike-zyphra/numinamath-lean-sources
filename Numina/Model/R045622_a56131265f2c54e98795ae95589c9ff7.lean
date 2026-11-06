import Mathlib

theorem algebra_270174 (θ₁ θ₂ θ₃ : ℝ) (h₁ : θ₁ = 117 * Real.pi / 180) (h₂ : θ₂ = 118 * Real.pi / 180)
    (h₃ : θ₃ = 125 * Real.pi / 180) :
    Real.tan θ₁ + Real.tan θ₂ + Real.tan θ₃ = Real.tan θ₁ * Real.tan θ₂ * Real.tan θ₃ := by
  have h₄ : θ₁ = 13 * Real.pi / 20 := by 
    rw [h₁]
    linarith [Real.pi_pos]
  have h₅ : θ₂ = 59 * Real.pi / 90 := by
    rw [h₂]
    linarith [Real.pi_pos]
  have h₆ : θ₃ = 25 * Real.pi / 36 := by
    rw [h₃]
    linarith [Real.pi_pos]
  have h₇ : Real.tan θ₁ = - Real.tan (7 * Real.pi / 20) := by 
    rw [h₄]
    have h₈ : 13 * Real.pi / 20 = Real.pi - (7 * Real.pi / 20) := by
      nlinarith [Real.pi_pos]
    rw [h₈]
    have h₉ : Real.tan (Real.pi - (7 * Real.pi / 20)) = - Real.tan (7 * Real.pi / 20) := by
      rw [Real.tan_pi_sub]
    linarith [h₉]
  have h₈ : Real.tan θ₂ = - Real.tan (31 * Real.pi / 90) := by
    rw [h₅]
    have h₉ : 59 * Real.pi / 90 = Real.pi - (31 * Real.pi / 90) := by
      nlinarith [Real.pi_pos]
    rw [h₉]
    have h₁₀ : Real.tan (Real.pi - (31 * Real.pi / 90)) = - Real.tan (31 * Real.pi / 90) := by 
      rw [Real.tan_pi_sub]
    linarith [h₁₀]
  have h₉ : Real.tan θ₃ = - Real.tan (11 * Real.pi / 36) := by 
    rw [h₆]
    have h₁₀ : 25 * Real.pi / 36 = Real.pi - (11 * Real.pi / 36) := by 
      nlinarith [Real.pi_pos]
    rw [h₁₀]
    have h₁₁ : Real.tan (Real.pi - (11 * Real.pi / 36)) = - Real.tan (11 * Real.pi / 36) := by 
      rw [Real.tan_pi_sub]
    linarith [h₁₁]
  have h₁₂ : 7 * Real.pi / 20 + 31 * Real.pi / 90 + 11 * Real.pi / 36 = Real.pi := by
    linarith [Real.pi_pos]
  have h₁₃ : Real.tan (7 * Real.pi / 20) + Real.tan (31 * Real.pi / 90) + Real.tan (11 * Real.pi / 36) = Real.tan (7 * Real.pi / 20) * Real.tan (31 * Real.pi / 90) * Real.tan (11 * Real.pi / 36) := by 
    have h₄ : 7 * Real.pi / 20 + 31 * Real.pi / 90 + 11 * Real.pi / 36 = Real.pi := by
      linarith [Real.pi_pos]
    have h₁₄ : Real.tan (7 * Real.pi / 20) + Real.tan (31 * Real.pi / 90) + Real.tan (11 * Real.pi / 36) = Real.tan (7 * Real.pi / 20) * Real.tan (31 * Real.pi / 90) * Real.tan (11 * Real.pi / 36) := by 
      have h₄ : 7 * Real.pi / 20 + 31 * Real.pi / 90 + 11 * Real.pi / 36 = Real.pi := by
        linarith [Real.pi_pos]
      have h₃ : Real.tan (7 * Real.pi / 20) = Real.sin (7 * Real.pi / 20) / Real.cos (7 * Real.pi / 20) := by
        rw [Real.tan_eq_sin_div_cos]
      have h₄ : Real.tan (31 * Real.pi / 90) = Real.sin (31 * Real.pi / 90) / Real.cos (31 * Real.pi / 90) := by
        rw [Real.tan_eq_sin_div_cos]
      have h₅ : Real.tan (11 * Real.pi / 36) = Real.sin (11 * Real.pi / 36) / Real.cos (11 * Real.pi / 36) := by 
        rw [Real.tan_eq_sin_div_cos]
      rw [h₃, h₄, h₅]
      have h₆ : Real.cos (7 * Real.pi / 20) ≠ 0 := by 
        have h₇ : 0 < 7 * Real.pi / 20 := by 
          nlinarith [Real.pi_pos]
        have h₈ : 7 * Real.pi / 20 < Real.pi := by 
          nlinarith [Real.pi_pos]
        apply ne_of_gt
        apply Real.cos_pos_of_mem_Ioo
        constructor
        linarith
        linarith
      have h₇ : Real.cos (31 * Real.pi / 90) ≠ 0 := by 
        have h₈ : 0 < 31 * Real.pi / 90 := by 
          nlinarith [Real.pi_pos]
        have h₉ : 31 * Real.pi / 90 < Real.pi := by 
          nlinarith [Real.pi_pos]
        apply ne_of_gt
        apply Real.cos_pos_of_mem_Ioo
        constructor
        linarith
        linarith
      have h₈ : Real.cos (11 * Real.pi / 36) ≠ 0 := by 
        have h₉ : 0 < 11 * Real.pi / 36 := by 
          nlinarith [Real.pi_pos]
        have h₁₀ : 11 * Real.pi / 36 < Real.pi := by 
          nlinarith [Real.pi_pos]
        apply ne_of_gt
        apply Real.cos_pos_of_mem_Ioo
        constructor
        linarith
        linarith
      have h₉ : Real.sin (7 * Real.pi / 20) * Real.cos (31 * Real.pi / 90) * Real.cos (11 * Real.pi / 36) + Real.cos (7 * Real.pi / 20) * Real.sin (31 * Real.pi / 90) * Real.cos (11 * Real.pi / 36) + Real.cos (7 * Real.pi / 20) * Real.cos (31 * Real.pi / 90) * Real.sin (11 * Real.pi / 36) = Real.sin (7 * Real.pi / 20) * Real.sin (31 * Real.pi / 90) * Real.sin (11 * Real.pi / 36) := by 
        have h₅ : 7 * Real.pi / 20 + 31 * Real.pi / 90 + 11 * Real.pi / 36 = Real.pi := by
          linarith [Real.pi_pos]
        have h₆ : Real.sin ((7 * Real.pi / 20) + (31 * Real.pi / 90) + (11 * Real.pi / 36)) = 0 := by
          rw [h₅]
          simp
        have h₇ : Real.sin ((7 * Real.pi / 20) + (31 * Real.pi / 90) + (11 * Real.pi / 36)) = Real.sin (7 * Real.pi / 20) * Real.cos (31 * Real.pi / 90) * Real.cos (11 * Real.pi / 36) + Real.cos (7 * Real.pi / 20) * Real.sin (31 * Real.pi / 90) * Real.cos (11 * Real.pi / 36) + Real.cos (7 * Real.pi / 20) * Real.cos (31 * Real.pi / 90) * Real.sin (11 * Real.pi / 36) - Real.sin (7 * Real.pi / 20) * Real.sin (31 * Real.pi / 90) * Real.sin (11 * Real.pi / 36) := by 
          simp [Real.sin_add, Real.cos_add, add_mul, mul_add, mul_assoc]
          <;> ring
        linarith [h₆, h₇]
      field_simp [h₆, h₇, h₈]
      <;> nlinarith
    linarith
  rw [h₇, h₈, h₉]
  nlinarith [h₁₃]