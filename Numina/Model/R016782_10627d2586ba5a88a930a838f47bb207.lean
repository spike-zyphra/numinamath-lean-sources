import Mathlib

theorem algebra_185816 (α : ℝ) :
    (4 * Real.sin (α - 5 * Real.pi) ^ 2 - Real.sin (2 * α + Real.pi) ^ 2) /
    (Real.cos (2 * α - 3 * Real.pi / 2) ^ 2 - 4 + 4 * Real.sin α ^ 2) =
    -Real.tan α ^ 4 := by
  have h1 : Real.sin (α - 5 * Real.pi) = - Real.sin α := by 
    have h1 : Real.sin (α - 5 * Real.pi) = Real.sin (α - Real.pi - 4 * Real.pi) := by
      ring_nf
    rw [h1]
    have h2 : Real.sin (α - Real.pi - 4 * Real.pi) = Real.sin (α - Real.pi - 2 * Real.pi - 2 * Real.pi) := by
      ring_nf
    rw [h2]
    rw [show Real.sin (α - Real.pi - 2 * Real.pi - 2 * Real.pi) = Real.sin (α - Real.pi - 2 * Real.pi) by rw [show α - Real.pi - 2 * Real.pi - 2 * Real.pi = (α - Real.pi - 2 * Real.pi) - 2 * Real.pi by ring]; rw [Real.sin_sub_two_pi]]
    <;> rw [show Real.sin (α - Real.pi - 2 * Real.pi) = Real.sin (α - Real.pi) by rw [show α - Real.pi - 2 * Real.pi = (α - Real.pi) - 2 * Real.pi by ring]; rw [Real.sin_sub_two_pi]]
    <;> rw [Real.sin_sub, Real.sin_pi, Real.cos_pi]
    <;> ring
  have h2 : Real.sin (2 * α + Real.pi) = - (2 * Real.sin α * Real.cos α) := by
    have h7 : Real.sin (2 * α + Real.pi) = - Real.sin (2 * α) := by
      rw [show 2 * α + Real.pi = 2 * α + Real.pi by ring, Real.sin_add, Real.sin_pi, Real.cos_pi]
      ring
    rw [h7]
    have h8 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by 
      rw [Real.sin_two_mul]
    rw [h8]
    <;> ring_nf
  have h3 : Real.cos (2 * α - 3 * Real.pi / 2) = - (2 * Real.sin α * Real.cos α) := by 
    have h4 : 2 * α - 3 * Real.pi / 2 = (2 * α - Real.pi / 2) - Real.pi := by
      linarith [Real.pi_pos]
    rw [h4]
    have h5 : Real.cos ((2 * α - Real.pi / 2) - Real.pi) = - Real.cos (2 * α - Real.pi / 2) := by 
      rw [Real.cos_sub_pi]
    rw [h5]
    have h6 : Real.cos (2 * α - Real.pi / 2) = Real.sin (2 * α) := by 
      have h7 : Real.cos (2 * α - Real.pi / 2) = Real.sin (2 * α) := by
        rw [show 2 * α - Real.pi / 2 = 2 * α - Real.pi / 2 by ring]
        rw [Real.cos_sub_pi_div_two]
      rw [h7]
    rw [h6]
    have h7 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by
      rw [Real.sin_two_mul]
    rw [h7]
    <;> ring_nf <;> simp [Real.sin_sq, Real.cos_sq]
    <;> ring_nf
  have eq1 : 4 * Real.sin (α - 5 * Real.pi) ^ 2 - Real.sin (2 * α + Real.pi) ^ 2 = 4 * Real.sin α ^ 4 := by
    rw [h1, h2]
    have eq2 : 4 * (-Real.sin α) ^ 2 - (-(2 * Real.sin α * Real.cos α)) ^ 2 = 4 * Real.sin α ^ 4 := by
      have h3 : (-(Real.sin α)) ^ 2 = Real.sin α ^ 2 := by ring
      have h4 : (-(2 * Real.sin α * Real.cos α)) ^ 2 = (2 * Real.sin α * Real.cos α) ^ 2 := by 
        ring_nf 
      rw [h3, h4]
      have h5 : (2 * Real.sin α * Real.cos α) ^ 2 = 4 * (Real.sin α ^ 2 * Real.cos α ^ 2) := by 
        ring_nf 
      have h6 : Real.sin α ^ 2 * (1 - Real.cos α ^ 2) = Real.sin α ^ 4 := by
        have h7 : (1 - Real.cos α ^ 2) = Real.sin α ^ 2 := by
          have h8 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
          linarith
        rw [h7]
        <;> nlinarith [Real.sin_sq_add_cos_sq α]
      have h7 : 4 * Real.sin α ^ 2 - 4 * (Real.sin α ^ 2 * Real.cos α ^ 2) = 4 * (Real.sin α ^ 2 * (1 - Real.cos α ^ 2)) := by 
        ring
      rw [h5] at *
      nlinarith [h6, h7, Real.sin_sq_add_cos_sq α]
    linarith [eq2]
  have eq2 : Real.cos (2 * α - 3 * Real.pi / 2) ^ 2 - 4 + 4 * Real.sin α ^ 2 = -4 * Real.cos α ^ 4 := by
    rw [h3]
    have h4 : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by
      have h5 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
      linarith
    have h5 : (-(2 * Real.sin α * Real.cos α)) ^ 2 = (2 * Real.sin α * Real.cos α) ^ 2 := by 
      ring_nf
    rw [h5]
    have h6 : (2 * Real.sin α * Real.cos α) ^ 2 = 4 * (Real.sin α ^ 2) * (Real.cos α ^ 2) := by
      ring_nf
    rw [h6]
    rw [show Real.sin α ^ 2 = 1 - Real.cos α ^ 2 by linarith [h4]] at *
    nlinarith [sq_nonneg (Real.sin α ^ 2 - 1), sq_nonneg (Real.cos α ^ 2 - 1), Real.sin_sq_add_cos_sq α, sq_nonneg (Real.sin α * Real.cos α)]
  rw [eq1, eq2]
  have htan : Real.tan α = Real.sin α / Real.cos α := by
    rw [Real.tan_eq_sin_div_cos]
  rw [htan]
  field_simp [Real.cos_sq_add_sin_sq α]
  <;> ring_nf
  <;> field_simp [Real.cos_sq_add_sin_sq α]
  <;> nlinarith [Real.sin_sq_add_cos_sq α, sq_nonneg (Real.sin α ^ 2 - 1), sq_nonneg (Real.cos α ^ 2 - 1), sq_nonneg (Real.sin α * Real.cos α)]