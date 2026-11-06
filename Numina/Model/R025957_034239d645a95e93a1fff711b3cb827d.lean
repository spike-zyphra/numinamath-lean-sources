import Mathlib

theorem algebra_244387 {a b c d : ℝ} (h₀ : a + c = -4) (h₁ : a * c + b + d = 6)
    (h₂ : a * d + b * c = -5) (h₃ : b * d = 2) :
    (a = -3 ∧ b = 2 ∧ c = -1 ∧ d = 1) ∨ (a = -1 ∧ b = 1 ∧ c = -3 ∧ d = 2) := by
  have h4 : c = -4 - a := by linarith
  rw [h4] at h₁ h₂
  have h5 : b + d = 6 + 4 * a + a ^ 2 := by nlinarith
  have h6 : a * d -4 * b - a * b = -5 := by nlinarith 
  have h8 : (a + 3) * (a + 1) = 0 := by nlinarith [sq_nonneg (b - d), sq_nonneg (a + 1), sq_nonneg (a + 3), sq_nonneg (b -1), sq_nonneg (d - 1)]
  cases' (mul_eq_zero.1 h8) with h9 h10 
  · -- a + 3 = 0
    have ha1 : a = -3 := by linarith 
    have c1 : c = -1 := by nlinarith 
    have hd1 : d = 1 := by 
      have h9a : b + d = 3 := by 
        rw [ha1] at h5 
        nlinarith 
      have h9b : b + 3 * d = 5 := by 
        rw [ha1] at h6 
        nlinarith 
      nlinarith 
    have hb1 : b = 2 := by 
      have h9a : b + d = 3 := by 
        rw [ha1] at h5 
        nlinarith 
      nlinarith [hd1]
    left 
    constructor 
    · -- a = -3 
      linarith 
    constructor 
    · -- b = 2 
      linarith 
    constructor 
    · -- c = -1 
      linarith 
    · -- d = 1 
      linarith 
  · -- a + 1 = 0 
    have ha2 : a = -1 := by linarith 
    have c2 : c = -3 := by 
      rw [ha2] at h4 
      nlinarith 
    have hd2 : d = 2 := by 
      have h9a : b + d = 3 := by 
        rw [ha2] at h5 
        nlinarith 
      have h9b : d + 3 * b = 5 := by 
        rw [ha2] at h6 
        nlinarith 
      nlinarith 
    have hb2 : b = 1 := by 
      have h9a : b + d = 3 := by 
        rw [ha2] at h5 
        nlinarith 
      nlinarith [hd2]
    right 
    constructor 
    · -- a = -1 
      linarith 
    constructor 
    · -- b = 1 
      linarith 
    constructor 
    · -- c = -3 
      linarith 
    · -- d = 2 
      linarith