import Mathlib

theorem algebra_162451 (α : Real) : 16 * Real.sin α ^ 5 - 20 * Real.sin α ^ 3 + 5 * Real.sin α = Real.sin (5 * α) := by
  have h1 : Real.sin (5 * α) = 16 * Real.sin α ^ 5 - 20 * Real.sin α ^ 3 + 5 * Real.sin α := by
    have h2 : Real.sin (5 * α) = Real.sin (2 * α + 3 * α) := by
      ring_nf
    rw [h2]
    have h3 : Real.sin (2 * α + 3 * α) = Real.sin (2 * α) * Real.cos (3 * α) + Real.cos (2 * α) * Real.sin (3 * α) := by
      rw [Real.sin_add]
    rw [h3]
    have h4 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by
      rw [show 2 * α = 2 * α by ring]
      simp [Real.sin_two_mul]
    have h5 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := h4
    have h6 : Real.cos (3 * α) = 4 * Real.cos α ^ 3 - 3 * Real.cos α := by
      have hcos3a : Real.cos (3 * α) = 4 * Real.cos α ^ 3 - 3 * Real.cos α := by
        rw [Real.cos_three_mul]
      exact hcos3a
    have h7 : Real.sin (3 * α) = 3 * Real.sin α - 4 * Real.sin α ^ 3 := by
      have hsin3a : Real.sin (3 * α) = 3 * Real.sin α - 4 * Real.sin α ^ 3 := by
        rw [Real.sin_three_mul]
      exact hsin3a
    have h8 : Real.cos (2 * α) = 1 - 2 * Real.sin α ^ 2 := by
      have hcos2a : Real.cos (2 * α) = 1 - 2 * Real.sin α ^ 2 := by
        rw [Real.cos_two_mul, Real.sin_sq]
        <;> ring_nf
      exact hcos2a
    rw [h4, h6, h8, h7]
    have h9 : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := by
      rw [←Real.sin_sq_add_cos_sq α]
      linarith
    have eq1 : Real.cos α ^ 4 = (1 - Real.sin α ^ 2) ^ 2 := by
      calc
        Real.cos α ^ 4 = (Real.cos α ^ 2) ^ 2 := by ring
        _ = (1 - Real.sin α ^ 2) ^ 2 := by rw [h9]
    ring_nf
    <;> simp [pow_two, pow_three, pow_succ, h9, eq1, mul_add, mul_sub]
    <;> ring_nf
    <;> nlinarith [Real.sin_sq_add_cos_sq α, sq_nonneg (Real.cos α ^ 2 - 1), sq_nonneg (Real.sin α ^ 2 - 1)]
  linarith [h1]