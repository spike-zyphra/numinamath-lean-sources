import Mathlib

theorem algebra_274525 {a b c r : ℝ} (h₀ : a + b + c = 114) (h₁ : a * b * c = 46656)
    (h₂ : b = a * r) (h₃ : c = a * r ^ 2) : a + c = 78 := by

  have h4 : a * b * c = a * (a * r) * (a * r ^ 2) := by
    rw [h₂, h₃]
  
  rw [h4] at h₁
  
  have h5 : a ^ 3 * r ^ 3 = 46656 := by
    ring_nf at h₁ ⊢
    linarith
  
  have h6 : a * r = 36 := by
    have h7 : a ^ 3 * r ^ 3 = (a * r) ^ 3 := by ring
    rw [h7] at h5
    have h8 : (a * r) ^ 3 - 46656 = 0 := by linarith
    have h9 : (a * r - 36) * ((a * r) ^ 2 + (a * r) * 36 + 36 ^ 2) = 0 := by
      ring_nf at h8 ⊢
      nlinarith
  
    cases' (mul_eq_zero.mp h9) with h10 h11
  
    · -- case where a * r - 36 = 0, so a * r = 36
      linarith
  
    · -- case where (a * r)^2 + (a * r) * 36 + 36^2 = 0
      have h12 : (a * r + 18) ^ 2 + 27 * 36 = 0 := by 
        nlinarith
  
      have h13 : (a * r + 18) ^ 2 ≥ 0 := by apply sq_nonneg
  
      nlinarith
  
  have sum_eq : a + (a * r) + (a * r ^ 2) = 114 := by
    have h6' : a + b + c = 114 := h₀
    rw [h₂, h₃] at h6'
    nlinarith
  
  have h7 : a + c = a + (a * r ^ 2) := by
    rw [h₃]
  
  have h13 : a + c = 78 := by 
    nlinarith [sum_eq, h6]

  linarith