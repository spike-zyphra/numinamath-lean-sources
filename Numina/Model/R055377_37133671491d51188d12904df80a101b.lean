import Mathlib

theorem algebra_14107 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : c = 6 * Real.sqrt 2) (h₅ : Real.arctan (a / b) = Real.pi / 4) :
    (1 / 2) * a * b = 18 := by
  have h₀₀ : a / b = 1 := by
    have h_eq : a / b = Real.tan (Real.pi / 4) := by
      have h : Real.arctan (a / b) = Real.pi / 4 := by 
        linarith [h₅]
      have h_tan : a / b = Real.tan (Real.arctan (a / b)) := by
        field_simp [Real.tan_arctan]
      rw [h] at h_tan
      linarith [h_tan]
    rw [Real.tan_pi_div_four] at h_eq
    linarith [h_eq]
  have h₁₁ : a = b := by
    have hb : b > 0 := by exact_mod_cast h₁
    have : a / b = 1 := by
      linarith [h₀₀]
    have h_eq : a = b := by
      field_simp [(show b ≠ 0 by linarith)] at this ⊢
      <;> nlinarith
    linarith [h_eq]
  have h₇ : c^2 = 72 := by
    rw [h₄]
    have h_eq : (6 * Real.sqrt 2) ^ 2 = 72 := by
      calc 
        (6 * Real.sqrt 2) ^ 2 = 6^2 * (Real.sqrt 2)^2 := by ring
        _ = 36 * 2 := by norm_num [Real.sq_sqrt]
        _ = 72 := by norm_num
    linarith [h_eq]
  have h₂₂ : a^2 + b^2 = 72 := by
    nlinarith [h₃, h₇]
  have h₁₃ : 2 * a^2 = 72 := by
    rw [show b = a by linarith [h₁₁]] at h₂₂ 
    nlinarith 
  have h₁₄ : a^2 = 36 := by 
    nlinarith 
  have h₈ : a * b = 36 := by 
    have : b = a := by linarith [h₁₁]
    rw [this]
    nlinarith [h₁₄]
  linarith [h₈]