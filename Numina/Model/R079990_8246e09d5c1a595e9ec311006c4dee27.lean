import Mathlib

theorem algebra_233861 (d w b : ℝ) (h₀ : d > 0) (h₁ : w > 0) (h₂ : b > 0)
    (h₃ : d / 2 / w + d / 2 / b = 5.5) (h₄ : d / b = 1) :
    d / w = 10 := by 
  have h₅ : d = b := by 
    have h6 : d / b = 1 := h₄
    field_simp at h6 
    linarith 
  rw [h₅] at h₃ 
  have h₆ : b / 2 / b = 1 / 2 := by 
    field_simp 
    <;> linarith 
  have h₇ : b / 2 / w + 1 / 2 = 5.5 := by 
    calc 
      b / 2 / w + 1 / 2 = b / 2 / w + b / 2 / b := by rw [h₆]
      _ = 5.5 := h₃ 
  have h₈ : b / 2 / w = 5 := by 
    calc 
      b / 2 / w = b / 2 / w + 1 / 2 - 1 / 2 := by ring 
      _ = 5.5 - 1 / 2 := by rw [h₇]
      _ = 5 := by norm_num 
  have h₉ : b / w = 10 := by 
    have h₁₀ : b / 2 / w = 5 := h₈ 
    have h₁₁ : b = 10 * w := by 
      have h₁₂ : b / 2 / w = 5 := h₁₀ 
      have h₁₃ : b / 2 / w = (b) / (2 * w) := by 
        ring_nf 
        <;> field_simp [show w ≠ 0 by linarith] 
        <;> ring 
      rw [h₁₃] at h₁₂ 
      have h₁₄ : b = 10 * w := by 
        have h₁₅ : 2 * w ≠ 0 := by 
          nlinarith 
        field_simp at h₁₂ 
        nlinarith 
      linarith 
    have h₁₂ : b / w = 10 := by 
      have h₁₃ : b = 10 * w := h₁₁ 
      rw [h₁₃] 
      field_simp 
      <;> nlinarith 
    linarith 
  have h₁₀ : d / w = b / w := by 
    rw [show d = b by linarith [h₅]]
  rw [h₁₀] 
  linarith [h₉]