import Mathlib

theorem algebra_196565 (x : ℝ) (hx : Real.pi / 2 > x ∧ x > 0) (h : Real.cos (x - 3 * Real.pi / 2) = -4 / 5) :
    Real.sin (x / 2) * Real.cos (5 * x / 2) = -38 / 125 := by
  have h1 : Real.sin x = 4 / 5 := by 
    have h2 : Real.cos (x - 3 * Real.pi / 2) = -4 / 5 := h
    have h3 : Real.cos (x - 3 * Real.pi / 2) = Real.sin x * (-1) := by 
      have h4 : Real.cos (x - 3 * Real.pi / 2) = Real.cos ( (x - Real.pi) - Real.pi / 2 ) := by 
        ring_nf
      rw [h4]
      have h5 : Real.cos ( (x - Real.pi) - Real.pi / 2 ) = Real.sin (x - Real.pi) := by 
        rw [Real.cos_sub_pi_div_two]
      rw [h5]
      have h6 : Real.sin (x - Real.pi) = - Real.sin x := by 
        rw [Real.sin_sub, Real.sin_pi, Real.cos_pi]
        ring_nf
      rw [h6]
      all_goals linarith
    rw [h3] at h2
    nlinarith 
  have hcosx : Real.cos x = 3 / 5 := by 
    have hcos2 : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
    rw [h1] at hcos2
    have hx3 : Real.cos x > 0 := by 
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [hx.2, hx.1, Real.pi_pos]
      · linarith [hx.2, hx.1, Real.pi_pos]
    nlinarith [sq_nonneg (Real.cos x), sq_nonneg (Real.sin x), hcos2]
  have hsin2x : Real.sin (2 * x) = 24 / 25 := by 
    rw [Real.sin_two_mul]
    rw [h1, hcosx]
    norm_num
  have hsin3x : Real.sin (3 * x) = 44 / 125 := by 
    have h7 : Real.sin (3 * x) = 3 * Real.sin x - 4 * Real.sin x ^ 3 := by 
      rw [Real.sin_three_mul]
    rw [h7, h1]
    norm_num
    <;> ring_nf <;> norm_num
  have h8 : Real.sin (x / 2) * Real.cos (5 * x / 2) = (1 / 2) * (Real.sin (3 * x) - Real.sin (2 * x)) := by
    have h9 : Real.sin (x / 2) * Real.cos (5 * x / 2) = (1 / 2) * (Real.sin ( (x / 2) + (5 * x / 2) ) + Real.sin ( (x / 2) - (5 * x / 2) )) := by 
      rw [Real.sin_add, Real.sin_sub]
      ring_nf
      <;> simp [Real.sin_add, Real.sin_sub]
      <;> ring_nf 
    have h10 : (x / 2) + (5 * x / 2) = 3 * x := by ring
    have h11 : (x / 2) - (5 * x / 2) = - (2 * x) := by ring
    rw [h10, h11] at h9
    have h12 : Real.sin (- (2 * x)) = - Real.sin (2 * x) := by 
      rw [Real.sin_neg]
    rw [h12] at h9 
    linarith 
  rw [h8]
  rw [hsin2x, hsin3x]
  norm_num
  all_goals norm_num
  <;> ring_nf <;> norm_num