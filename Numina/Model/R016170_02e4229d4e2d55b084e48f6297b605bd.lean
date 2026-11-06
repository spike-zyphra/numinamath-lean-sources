import Mathlib

theorem algebra_185993 (α : ℝ) :
    1 - Real.cos (2 * α - 270 / 180 * Real.pi) + Real.sin (2 * α + 270 / 180 * Real.pi) =
    2 * Real.sqrt 2 * Real.sin α * Real.cos (45 / 180 * Real.pi - α) := by

  have h1 : Real.cos (2 * α - 270 / 180 * Real.pi) = - Real.sin (2 * α) := by
    have h2 : 2 * α - 270 / 180 * Real.pi = 2 * α + Real.pi / 2 - 2 * Real.pi := by
      ring_nf
      <;> field_simp [Real.pi_pos]
      <;> ring
    rw [h2]
    have h3 : Real.cos (2 * α + Real.pi / 2 - 2 * Real.pi) = Real.cos (2 * α + Real.pi / 2) := by
      have h4 : Real.cos (2 * α + Real.pi / 2 - 2 * Real.pi) = Real.cos (2 * α + Real.pi / 2) := by
        have h6 : 2 * α + Real.pi / 2 - 2 * Real.pi = (2 * α + Real.pi / 2) - 2 * Real.pi := by ring
        rw [h6]
        have h7 : Real.cos ((2 * α + Real.pi / 2) - 2 * Real.pi) = Real.cos (2 * α + Real.pi / 2) := by
          have h8 : Real.cos ((2 * α + Real.pi / 2) - 2 * Real.pi) = Real.cos (2 * α + Real.pi / 2) := by
            rw [show (2 * α + Real.pi / 2) - 2 * Real.pi = (2 * α + Real.pi / 2) - 2 * Real.pi by ring]
            have h9 : Real.cos ((2 * α + Real.pi / 2) - 2 * Real.pi) = Real.cos (2 * α + Real.pi / 2) := by
              rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
              <;> simp <;> ring_nf
            exact h9
          exact h8
        exact h7
      exact h4
    rw [h3]
    rw [Real.cos_add]
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
    <;> ring_nf <;> simp <;> ring_nf <;> simp
  have h2 : Real.sin (2 * α + 270 / 180 * Real.pi) = - Real.cos (2 * α) := by
    have h3 : 2 * α + 270 / 180 * Real.pi = 2 * α - Real.pi / 2 + 2 * Real.pi := by
      ring_nf
      <;> field_simp [Real.pi_pos]
      <;> ring
    rw [h3]
    have h4 : Real.sin (2 * α - Real.pi / 2 + 2 * Real.pi) = Real.sin (2 * α - Real.pi / 2) := by
      have h5 : Real.sin (2 * α - Real.pi / 2 + 2 * Real.pi) = Real.sin (2 * α - Real.pi / 2) := by
        rw [Real.sin_add, Real.cos_two_pi, Real.sin_two_pi]
        <;> simp
        <;> ring_nf
        <;> simp
      exact h5
    rw [h4]
    rw [Real.sin_sub]
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
    <;> ring_nf <;> simp <;> ring_nf <;> simp
  
  rw [h1, h2]

  have h3 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by
    rw [Real.sin_two_mul]

  have h4 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by
    rw [Real.cos_two_mul]

  rw [h3, h4]

  have h5 : Real.cos (45 / 180 * Real.pi - α) = Real.cos (45 / 180 * Real.pi) * Real.cos α + Real.sin (45 / 180 * Real.pi) * Real.sin α := by
    rw [Real.cos_sub]

  have h6 : Real.cos (45 / 180 * Real.pi) = Real.sqrt 2 / 2 := by
    have h1 : 45 / 180 * Real.pi = Real.pi / 4 := by
      linarith [Real.pi_pos]
    rw [h1]
    exact Real.cos_pi_div_four

  have h7 : Real.sin (45 / 180 * Real.pi) = Real.sqrt 2 / 2 := by
    have h1 : 45 / 180 * Real.pi = Real.pi / 4 := by
      linarith [Real.pi_pos]
    rw [h1]
    exact Real.sin_pi_div_four
  
  rw [h5, h6, h7]

  have h8 : 2 * Real.sqrt 2 * Real.sin α * (Real.sqrt 2 / 2 * Real.cos α + Real.sqrt 2 / 2 * Real.sin α) = 2 * Real.sin α * (Real.cos α + Real.sin α) := by
    ring_nf
    <;> simp [Real.sqrt_sq]
    <;> ring_nf <;> simp
    <;> ring_nf <;> simp 
    all_goals 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), sq_nonneg (Real.sqrt 2 * Real.sin α), sq_nonneg (Real.sqrt 2 * Real.cos α), Real.sin_sq_add_cos_sq α, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith [h8, Real.sin_sq_add_cos_sq α, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (Real.sin α * Real.cos α), sq_nonneg (Real.sin α * (Real.sin α)), sq_nonneg (Real.sqrt 2 * Real.sin α), sq_nonneg (Real.sqrt 2 * Real.cos α), Real.sin_sq_add_cos_sq α]