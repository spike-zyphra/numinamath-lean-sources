import Mathlib

theorem algebra_8819
    (a m : ℝ)
    (h₀ : Real.sin a + Real.cos a = m) :
    Real.sin a ^ 3 + Real.cos a ^ 3 = m * (3 - m ^ 2) / 2 := by

  have h1 : Real.sin a ^ 3 + Real.cos a ^ 3 = (Real.sin a + Real.cos a) * (Real.sin a ^ 2 - Real.sin a * Real.cos a + Real.cos a ^ 2) := by
    ring
  have h2 : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
  have h3 : Real.sin a * Real.cos a = (m ^ 2 - 1) / 2 := by
    have h4 : (Real.sin a + Real.cos a) ^ 2 = m ^ 2 := by 
      rw [h₀]
    have h5 : (Real.sin a + Real.cos a) ^ 2 = Real.sin a ^ 2 + Real.cos a ^ 2 + 2 * (Real.sin a * Real.cos a) := by 
      ring
    rw [h5] at h4
    have h6 : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := h2
    rw [h6] at h4
    linarith
  have h6 : Real.sin a ^ 2 - Real.sin a * Real.cos a + Real.cos a ^ 2 = (3 - m ^ 2)/2 := by 
    have h7 : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := h2
    have h8 : Real.sin a * Real.cos a = (m ^ 2 - 1) / 2 := h3
    linarith
  rw [h1, h₀, h6]
  <;> ring_nf
  <;> linarith