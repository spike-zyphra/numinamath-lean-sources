import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_9239 (a : ℝ) (ha : a ≠ 0) (f : ℝ → ℝ)
  (hf : f = λ x => a * sin x - 1 / 2 * cos (2 * x) + a - 3 / a + 1 / 2)
  (h : ∀ x, f x ≤ 0) :
  0 < a ∧ a ≤ 1 := by
  have h1 := h (Real.pi / 2)
  simp [hf, Real.sin_pi_div_two, Real.cos_two_mul, Real.sin_pi, Real.cos_pi] at h1
  have h2 := h (0)
  simp [hf, Real.sin_zero, Real.cos_zero] at h2
  have h3 := h (Real.pi)
  simp [hf, Real.sin_pi, Real.cos_two_mul, Real.sin_pi, Real.cos_pi] at h3
  have h4 := h (Real.pi / 2 + Real.pi)
  have h5 : sin (Real.pi / 2 + Real.pi) = -1 := by
    rw [show Real.pi / 2 + Real.pi = Real.pi / 2 + Real.pi by ring]
    simp [sin_add, cos_pi, sin_pi]
    <;> ring
  have h6 : cos (2 * (Real.pi / 2 + Real.pi)) = -1 := by
    have : 2 * (Real.pi / 2 + Real.pi) = 3 * Real.pi := by ring
    rw [this]
    have : cos (3 * Real.pi) = -1 := by 
      have h1 : cos (3 * Real.pi) = cos (2 * Real.pi + Real.pi) := by ring
      rw [h1]
      simp [cos_add, cos_two_pi, sin_two_pi]
    linarith
  simp [hf, h5, h6] at h4
  
  have ha1 : 0 < a := by
    by_contra h2
    push_neg at h2
    have h3 : 3 / a ≤ 0 := by
      apply div_nonpos_of_nonneg_of_nonpos
      norm_num
      linarith
    have h7 : 3 / a ≥ 1 := by nlinarith [h4]
    linarith
  
  have ha2 : a ≤ 1 := by
    have h1a : 2 * a - 3 / a + 1 ≤ 0 := by linarith [h1]
    have h6 : 2 * a ^ 2 + a - 3 ≤ 0 := by
      have h7 : a * (2 * a - 3 / a + 1) ≤ 0 := by
        have ha1' : 0 < a := ha1
        have h8 : 2 * a - 3 / a + 1 ≤ 0 := by linarith
        nlinarith
      have : a * (2 * a - 3 / a + 1) = 2 * a ^ 2 + a - 3 := by
        field_simp at *
        ring
      linarith [this, h7]
    
    nlinarith [h6]

  constructor <;> linarith