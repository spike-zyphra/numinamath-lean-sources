import Mathlib

theorem algebra_310253 {x y : ℝ} (h : (x^2 + 6 * x + 12) * (5 * y^2 + 2 * y + 1) = 12 / 5) : x * y = 3 / 5 := by
  have h₁ : x ^ 2 + 6 * x + 12 = (x + 3) ^ 2 + 3 := by 
    ring
  have h₂ : 5 * y ^ 2 + 2 * y + 1 = 5 * (y + 1 / 5) ^ 2 + 4 / 5 := by 
    ring_nf
  rw [h₁, h₂] at h
  have h₃ : (x + 3) ^ 2 ≥ 0 := by 
    apply sq_nonneg
  have h₄ : 5 * (y + 1 / 5) ^ 2 ≥ 0 := by 
    nlinarith [sq_nonneg (y + 1 / 5)]
  have h₅ : (x + 3) ^ 2 = 0 := by 
    nlinarith [sq_nonneg ((x + 3) ^ 2), sq_nonneg (y + 1 / 5), h]
  have hx : x = -3 := by 
    have h₀ : (x + 3) ^ 2 = 0 := h₅ 
    have h₁ : x + 3 = 0 := by 
      rw [sq_eq_zero_iff] at h₀ 
      linarith 
    linarith 
  have h₀₀ : 5 * (y + 1 / 5) ^ 2 = 0 := by 
    nlinarith [h₅, h]
  have hy : y = -1 / 5 := by 
    have h₀₀₀ : (y + 1 / 5) ^ 2 = 0 := by 
      nlinarith [h₀₀] 
    have h₀₁ : y + 1 / 5 = 0 := by 
      rw [sq_eq_zero_iff] at h₀₀₀ 
      linarith 
    linarith 
  rw [hx, hy] 
  norm_num