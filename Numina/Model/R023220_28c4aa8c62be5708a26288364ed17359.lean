import Mathlib

theorem algebra_147152 (s : ℝ) (h₀ : s > 0) (v₁ v₂ v₃ : ℝ)
    (h₁ : v₁ > 0) (h₂ : v₂ > 0) (h₃ : v₃ > 0) (h₄ : v₁ ≠ v₂)
    (h₅ : v₂ ≠ v₃) (h₆ : v₃ ≠ v₁) :
    (3 * s) / (s / v₁ + s / v₂ + s / v₃) = 3 * v₁ * v₂ * v₃ / (v₁ * v₂ + v₂ * v₃ + v₁ * v₃) := by 
  have h7 : s / v₁ + s / v₂ + s / v₃ = s * (1 / v₁ + 1 / v₂ + 1 / v₃) := by 
    ring 
  rw [h7]
  have h8 : v₁ * v₂ * v₃ > 0 := by
    apply mul_pos
    apply mul_pos
    exact h₁
    exact h₂
    exact h₃
  have h9 : v₁ * v₂ + v₂ * v₃ + v₁ * v₃ > 0 := by 
    nlinarith [mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₁ h₃]
  field_simp [(show v₁ ≠ 0 by linarith), (show v₂ ≠ 0 by linarith), (show v₃ ≠ 0 by linarith), 
      show v₁ * v₂ + v₂ * v₃ + v₁ * v₃ ≠ 0 by 
        by_contra h
        have : v₁ * v₂ + v₂ * v₃ + v₁ * v₃ = 0 := by linarith 
        nlinarith [mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₁ h₃]
  ]
  <;> ring_nf <;> field_simp [(show v₁ ≠ 0 by linarith), (show v₂ ≠ 0 by linarith), 
      (show v₃ ≠ 0 by linarith)]
  <;> ring