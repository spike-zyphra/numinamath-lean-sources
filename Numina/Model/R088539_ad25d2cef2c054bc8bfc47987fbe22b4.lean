import Mathlib

theorem algebra_233066 (d v1 v2 : ℝ) (h₀ : d > 0) (h₁ : v1 > 0) (h₂ : v2 > 0)
    (h₃ : d / v1 = 12) (h₄ : d / v2 = 20) (h₅ : v1 * (t - 5) = v2 * t) :
    t = 12.5 := by
  have h6 : d = 12 * v1 := by
    have h7 : d / v1 = 12 := h₃
    field_simp [show v1 ≠ 0 by nlinarith] at h7 ⊢
    linarith

  have h7 : d = 20 * v2 := by
    have h8 : d / v2 = 20 := h₄
    field_simp [show v2 ≠ 0 by nlinarith] at h8 ⊢
    linarith
  
  have h8 : 12 * v1 = 20 * v2 := by linarith [h6, h7]

  have h9 : v1 = (5 / 3) * v2 := by
    linarith

  have h10 : (5 / 3) * v2 * (t - 5) = v2 * t := by
    rw [h9] at h₅
    linarith
  
  have h11 : (5 / 3) * (t - 5) = t := by
    apply (mul_left_inj' (show v2 ≠ 0 by nlinarith)).mp
    linarith
  
  have h12 : 2 * t = 25 := by
    linarith

  have ht : t = 25 / 2 := by
    linarith
  
  rw [ht]
  norm_num