import Mathlib

theorem algebra_186272 (α : ℝ) (hα : Real.sin (α - Real.pi / 2) = -2 / 3) (hα' : 270 * Real.pi / 180 < α ∧ α < 360 * Real.pi / 180) :
    1 / Real.tan (2 * α) = Real.sqrt 5 / 20 := by
  have h1 : Real.sin (α - Real.pi / 2) = -Real.cos α := by
    rw [Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  rw [h1] at hα
  have hcos : Real.cos α = 2 / 3 := by
    linarith
  have hα1 : 270 * Real.pi / 180 < α := hα'.left
  have hα2 : α < 360 * Real.pi / 180 := hα'.right
  have hsin2 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by
    rw [Real.sin_two_mul]
  have hcos2 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  have hsin : Real.sin α = - Real.sqrt 5 / 3 := by
    have h5' : Real.sin α ^ 2 = 5 / 9 := by
      have h5 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
      rw [hcos] at h5
      nlinarith
    have h6 : Real.sin α < 0 := by
      have hα1 : 3 * Real.pi / 2 < α := by
        linarith [hα'.left, Real.pi_pos]
      have hα2 : α < 2 * Real.pi := by
        linarith [hα'.right, Real.pi_pos]
      have h9 : Real.sin α < 0 := by
        have h10 : Real.sin α = - Real.sin (2 * Real.pi - α) := by
          rw [show 2 * Real.pi - α = 2 * Real.pi - α by rfl]
          rw [Real.sin_two_pi_sub]
          <;> ring_nf
        have h11 : Real.sin (2 * Real.pi - α) > 0 := by
          apply Real.sin_pos_of_pos_of_lt_pi
          . -- Show 0 < 2π - α
            nlinarith [Real.pi_pos, hα2]
          . -- Show 2π - α < π
            nlinarith [Real.pi_pos, hα2]
        nlinarith [h10, h11]
      linarith
    have h20 : Real.sin α = Real.sqrt (5 / 9) ∨ Real.sin α = - Real.sqrt (5 / 9) := by
      have h15 : (Real.sin α - Real.sqrt (5 / 9)) * (Real.sin α + Real.sqrt (5 / 9)) = 0 := by
        have h45 : Real.sqrt (5 / 9) ^ 2 = 5 / 9 := by
          rw [Real.sq_sqrt]
          norm_num
        nlinarith 
      cases (mul_eq_zero.mp h15) with
      | inl h =>
        left
        nlinarith 
      | inr h =>
        right
        nlinarith 
    cases h20 with
    | inl h4 =>
      nlinarith [show Real.sqrt (5 / 9) > 0 by
        apply Real.sqrt_pos.mpr
        norm_num
      ]
    | inr h6 =>
      have h15 : Real.sqrt (5 / 9) = Real.sqrt 5 / 3 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      rw [h15] at h6
      linarith
  have htan : Real.tan (2 * α) = Real.sin (2 * α) / Real.cos (2 * α) := by
    rw [Real.tan_eq_sin_div_cos]
  rw [htan]
  rw [hsin2, hcos2]
  rw [hsin, hcos]
  field_simp
  <;> ring_nf 
  <;> norm_num
  <;> ring_nf 
  <;> norm_num
  <;> ring_nf
  <;> norm_num