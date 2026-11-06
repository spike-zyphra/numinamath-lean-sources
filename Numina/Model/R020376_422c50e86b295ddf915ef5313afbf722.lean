import Mathlib

theorem algebra_185306 (α : ℝ) :
    Real.sin (α / 2) ^ 6 - Real.cos (α / 2) ^ 6 = (Real.sin α ^ 2 - 4) / 4 * Real.cos α := by
  have h1 : Real.sin (α / 2) ^ 2 + Real.cos (α / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α / 2)
  have h2 : Real.cos α = 2 * Real.cos (α / 2) ^ 2 - 1 := by
    have h3 : Real.cos α = Real.cos (2 * (α / 2)) := by 
      ring_nf
    rw [h3]
    rw [Real.cos_two_mul]
  have h3 : Real.cos (α / 2) ^ 2 = (1 + Real.cos α) / 2 := by
    linarith [h1, h2]
  have h4 : Real.sin (α / 2) ^ 2 = (1 - Real.cos α) / 2 := by 
    linarith [h1, h2]
  have eq1 : Real.sin (α / 2) ^ 6 - Real.cos (α / 2) ^ 6 =
      (Real.sin (α / 2) ^ 2 - Real.cos (α / 2) ^ 2) * 
      (Real.sin (α / 2) ^ 4 + Real.sin (α / 2) ^ 2 * Real.cos (α / 2) ^ 2 + Real.cos (α / 2) ^ 4) := by
    ring
  rw [eq1]
  have eq2 : Real.sin (α / 2) ^ 2 - Real.cos (α / 2) ^ 2 = - Real.cos α := by 
    have h3' : Real.sin (α / 2) ^ 2 = (1 - Real.cos α) / 2 := by
      linarith [h1, h2]
    have h4' : Real.cos (α / 2) ^ 2 = (1 + Real.cos α) / 2 := by 
      linarith [h1, h2]
    linarith [h3', h4']
  rw [eq2]
  have eq3 : Real.sin (α / 2) ^ 4 + Real.sin (α / 2) ^ 2 * Real.cos (α / 2) ^ 2 + Real.cos (α / 2) ^ 4 = 1 - Real.sin α ^ 2 / 4 := by
    have h5 : Real.sin (α / 2) ^ 2 = (1 - Real.cos α) / 2 := h4
    have h6 : Real.cos (α / 2) ^ 2 = (1 + Real.cos α) / 2 := h3
    have h7 : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by 
      have h8 : Real.sin α = Real.sin (2 * (α / 2)) := by 
        ring_nf
      rw [h8]
      rw [Real.sin_two_mul]
      <;> ring_nf
    have h9 : Real.sin α ^ 2 = 4 * (Real.sin (α / 2) ^ 2 * Real.cos (α / 2) ^ 2) := by
      calc
        Real.sin α ^ 2 = (2 * Real.sin (α / 2) * Real.cos (α / 2)) ^ 2 := by 
          rw [h7]
        _ = 4 * (Real.sin (α / 2) * Real.cos (α / 2)) ^ 2 := by 
          ring
        _ = 4 * (Real.sin (α / 2) ^ 2 * Real.cos (α / 2) ^ 2) := by 
          ring
    rw [show Real.sin (α / 2) ^ 4 + Real.sin (α / 2) ^ 2 * Real.cos (α / 2) ^ 2 + Real.cos (α / 2) ^ 4 = 
      (Real.sin (α / 2) ^ 2) ^ 2 + Real.sin (α / 2) ^ 2 * Real.cos (α / 2) ^ 2 + (Real.cos (α / 2) ^ 2) ^ 2 by ring]
    rw [show Real.sin (α / 2) ^ 2 = (1 - Real.cos α) / 2 by linarith [h1, h2] ]
    rw [show Real.cos (α / 2) ^ 2 = (1 + Real.cos α) / 2 by linarith [h1, h2] ]
    nlinarith [h9, Real.sin_sq_add_cos_sq α, h1, h2, sq_nonneg (Real.cos α ^ 2 - 1) ]
  rw [eq3]
  <;> ring