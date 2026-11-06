import Mathlib

theorem algebra_308162 {a : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = a^2 * Real.sin (2 * x) + (a - 2) * Real.cos (2 * x))
    (h : ∀ x, f (-Real.pi / 8 + x) = f (-Real.pi / 8 - x)) :
    a = 1 ∨ a = -2 := by
  have eq1 := h (Real.pi / 8)
  have eq2 : f (-Real.pi / 8 + Real.pi / 8) = f (-Real.pi / 8 - Real.pi / 8) := by
    simpa using eq1
  have eq3 : f (-Real.pi / 8 + Real.pi / 8) = a ^ 2 * Real.sin (2 * (-Real.pi / 8 + Real.pi / 8)) + (a - 2) * Real.cos (2 * (-Real.pi / 8 + Real.pi / 8)) := by
    apply hf
  have eq4 : f (-Real.pi / 8 - Real.pi / 8) = a ^ 2 * Real.sin (2 * (-Real.pi / 8 - Real.pi / 8)) + (a - 2) * Real.cos (2 * (-Real.pi / 8 - Real.pi / 8)) := by
    apply hf
  rw [eq3, eq4] at eq2
  have h1 : 2 * (-Real.pi / 8 + Real.pi / 8) = (0 : ℝ) := by ring_nf
  have h2 : 2 * (-Real.pi / 8 - Real.pi / 8) = (-Real.pi / 2 : ℝ) := by ring_nf
  rw [h1] at eq2
  rw [h2] at eq2
  have h3 : Real.sin (0 : ℝ) = 0 := Real.sin_zero
  have h4 : Real.cos (0 : ℝ) = 1 := Real.cos_zero
  have h5 : Real.sin (-Real.pi / 2 : ℝ) = -1 := by
    have h6 : Real.sin (-Real.pi / 2 : ℝ) = - Real.sin (Real.pi / 2 : ℝ) := by 
      rw [show -Real.pi / 2 = - (Real.pi / 2) by ring]
      rw [Real.sin_neg]
    have h7 : Real.sin (Real.pi / 2 : ℝ) = 1 := Real.sin_pi_div_two
    linarith
  have h6 : Real.cos (-Real.pi / 2 : ℝ) = 0 := by 
    have h7 : Real.cos (-Real.pi / 2 : ℝ) = Real.cos (Real.pi / 2 : ℝ) := by 
      rw [show -Real.pi / 2 = - (Real.pi / 2) by ring]
      rw [Real.cos_neg]
    have h8 : Real.cos (Real.pi / 2 : ℝ) = 0 := Real.cos_pi_div_two
    linarith
  simp [h3, h4, h5, h6] at eq2
  have h7 : a ^ 2 + a - 2 = 0 := by nlinarith 
  have : (a - 1) * (a + 2) = 0 := by nlinarith
  cases' (mul_eq_zero.mp this) with h8 h9
  · left 
    linarith
  · right 
    linarith