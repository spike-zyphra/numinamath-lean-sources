import Mathlib

theorem algebra_318506 {a b c : ℝ} (h₀ : a ≠ 0) (h₁ : b ≠ 0) (h₂ : c ≠ 0)
    (h₃ : a + b + c = 1) (h₄ : 1 / a + 1 / b + 1 / c = 1) :
    a = 1 ∨ b = 1 ∨ c = 1 := by
  have h5 : a * b + a * c + b * c = a * b * c := by
    field_simp [h₀, h₁, h₂] at h₄
    linarith
  
  have h7 : (a - 1) * (b - 1) * (c - 1) = 0 := by
    nlinarith [h₃, h5]
  
  cases' (mul_eq_zero.mp h7) with h8 h9
  cases' (mul_eq_zero.mp h8) with h10 h11
  
  · -- Case where a - 1 = 0, so a = 1
    left
    linarith
  
  · -- Case where b - 1 = 0, so b = 1
    right
    left
    linarith
  
  · -- Case where c - 1 = 0, so c = 1
    right
    right
    linarith