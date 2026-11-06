import Mathlib

theorem algebra_185591 (α : ℝ) :
    1 - Real.sin (α / 2 - 3 * Real.pi) - Real.cos (α / 4) ^ 2 +
    Real.sin (α / 4) ^ 2 =
    2 * Real.sqrt 2 * Real.sin (α / 4) * Real.sin ((α + Real.pi) / 4) := by

  have h1 : Real.sin (α / 2 - 3 * Real.pi) = - Real.sin (α / 2) := by
    have h2 : α / 2 - 3 * Real.pi = α / 2 - Real.pi - 2 * Real.pi := by ring
    rw [h2]
    have h3 : Real.sin (α / 2 - Real.pi - 2 * Real.pi) = Real.sin (α / 2 - Real.pi) := by
      rw [show α / 2 - Real.pi - 2 * Real.pi = (α / 2 - Real.pi) - 2 * Real.pi by ring]
      rw [Real.sin_sub_two_pi]
    have h4 : Real.sin (α / 2 - Real.pi) = - Real.sin (α / 2) := by 
      rw [Real.sin_sub, Real.sin_pi, Real.cos_pi]
      ring
    rw [h3, h4]

  have h2 : Real.cos (α / 4) ^ 2 - Real.sin (α / 4) ^ 2 = Real.cos (α / 2) := by
    have h3 : Real.cos (α / 2) = Real.cos (α / 4) ^ 2 - Real.sin (α / 4) ^ 2 := by 
      have h4 : α / 2 = 2 * (α / 4) := by ring
      rw [h4]
      rw [Real.cos_two_mul]
      <;> simp [Real.sin_sq]
      <;> ring
    linarith [h3]

  have eq1 : 1 - Real.sin (α / 2 - 3 * Real.pi) - Real.cos (α / 4) ^ 2 + Real.sin (α / 4) ^ 2 = 1 + Real.sin (α / 2) - Real.cos (α / 2) := by 
    have h3 : Real.sin (α / 2 - 3 * Real.pi) = - Real.sin (α / 2) := h1
    have h4 : Real.cos (α / 4) ^ 2 - Real.sin (α / 4) ^ 2 = Real.cos (α / 2) := h2
    linarith [h3, h4]

  rw [eq1]

  have h3 : Real.sin ((α + Real.pi) / 4) = Real.sin (α / 4) * Real.cos (Real.pi / 4) + Real.cos (α / 4) * Real.sin (Real.pi / 4) := by 
    have h4 : (α + Real.pi) / 4 = α / 4 + Real.pi / 4 := by ring
    rw [h4]
    rw [Real.sin_add]

  have h4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h5 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four

  rw [h3, h4, h5]

  have h6 : Real.sin (α / 2) = 2 * Real.sin (α / 4) * Real.cos (α / 4) := by
    have h7 : α / 2 = 2 * (α / 4) := by ring
    rw [h7]
    rw [Real.sin_two_mul]

  have h7 : Real.cos (α / 2) = 1 - 2 * Real.sin (α / 4) ^ 2 := by
    have h8 : α / 2 = 2 * (α / 4) := by ring
    rw [h8]
    rw [Real.cos_two_mul]
    rw [Real.cos_sq']
    <;> ring

  rw [h6, h7]

  ring_nf
  <;> simp [Real.sin_sq, Real.cos_sq]
  <;> ring