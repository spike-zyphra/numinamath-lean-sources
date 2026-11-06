import Mathlib

open Real

theorem calculus_23077 : cos (π / 18) * cos (π / 6) * cos (5 * π / 18) * cos (7 * π / 18) = 3 / 16 := by
  have h1 : cos (π / 6) = Real.sqrt 3 / 2 := by 
    exact Real.cos_pi_div_six 
  have h2 : cos (π / 18) * cos (5 * π / 18) * cos (7 * π / 18) = 1 / 4 * cos (π / 6) := by 
    have h4 : cos (π / 18) * cos (5 * π / 18) * cos (7 * π / 18) = 
          cos (π / 18) * cos (π / 3 - π / 18) * cos (π / 3 + π / 18) := by 
      ring_nf 
    rw [h4]
    have h5 : cos (π / 3 - π / 18) = (1 / 2) * cos (π / 18) + (Real.sqrt 3 / 2) * sin (π / 18) := by 
      rw [cos_sub]
      rw [cos_pi_div_three, sin_pi_div_three]
      <;> ring 
    have h6 : cos (π / 3 + π / 18) = (1 / 2) * cos (π / 18) - (Real.sqrt 3 / 2) * sin (π / 18) := by 
      rw [cos_add]
      rw [cos_pi_div_three, sin_pi_div_three]
      <;> ring 
    rw [h5, h6]
    have h10 : cos (3 * (π / 18)) = 4 * cos (π / 18) ^ 3 - 3 * cos (π / 18) := by 
      rw [cos_three_mul]
      <;> ring_nf
    have h9 : 3 * (π / 18) = π / 6 := by 
      ring 
    have h5 : cos (π / 18) * ((1 / 2) * cos (π / 18) + (Real.sqrt 3 / 2) * sin (π / 18)) * ((1 / 2) * cos (π / 18) - (Real.sqrt 3 / 2) * sin (π / 18)) = (1 / 4) * cos (π / 6) := by
      have htrig1 : sin (π / 18) ^ 2 = 1 - cos (π / 18) ^ 2 := by 
        have h : sin (π / 18) ^ 2 + cos (π / 18) ^ 2 = 1 := by 
          exact sin_sq_add_cos_sq (π / 18)
        linarith 
      have h3 : cos (π / 6) = 4 * cos (π / 18) ^ 3 - 3 * cos (π / 18) := by 
        have h4 : cos (π / 6) = cos (3 * (π / 18)) := by 
          rw [show 3 * (π / 18) = π / 6 by ring]
        rw [h4]
        have h5 : cos (3 * (π / 18)) = 4 * cos (π / 18) ^ 3 - 3 * cos (π / 18) := by 
          rw [cos_three_mul]
          <;> ring_nf 
        linarith [h5] 
      rw [h3]
      -- algebra manipulation 
      have h7 : cos (π / 18) * ((1 / 2) * cos (π / 18) + (Real.sqrt 3 / 2) * sin (π / 18)) * ((1 / 2) * cos (π / 18) - (Real.sqrt 3 / 2) * sin (π / 18)) = 
        cos (π / 18) * ( (1 / 4) * cos (π / 18) ^ 2 - (3 / 4) * sin (π / 18) ^ 2 ) := by 
        ring_nf 
        <;> simp [Real.sqrt_mul_self] 
        <;> ring 
      rw [h7]
      rw [htrig1]
      ring_nf 
      <;> simp [pow_two, mul_assoc, Real.sqrt_mul_self, mul_comm (cos (π / 18)), mul_assoc, pow_three]
      <;> ring_nf 
      <;> simp [Real.sqrt_pos.mpr, Real.sqrt_pos.mpr]
      <;> nlinarith [Real.sin_pos_of_pos_of_lt_pi (show 0 < π / 18 by linarith [Real.pi_pos] : (0 : ℝ) < π / 18), Real.sin_pos_of_pos_of_lt_pi (show 0 < π / 3 by linarith [Real.pi_pos] : (0 : ℝ) < π / 3)] 
    linarith 
  have h3 : cos (π / 18) * cos (5 * π / 18) * cos (7 * π / 18) = 1 / 4 * (Real.sqrt 3 / 2) := by 
    rw [h2] 
    rw [h1] 
  calc 
    cos (π / 18) * cos (π / 6) * cos (5 * π / 18) * cos (7 * π / 18) = cos (π / 6) * (cos (π / 18) * cos (5 * π / 18) * cos (7 * π / 18)) := by ring 
    _ = cos (π / 6) * (1 / 4 * (Real.sqrt 3 / 2)) := by rw [h3] 
    _ = (Real.sqrt 3 / 2) * (1 / 4 * (Real.sqrt 3 / 2)) := by rw [h1] 
    _ = 3 / 16 := by 
      nlinarith [Real.mul_self_sqrt (show 0 ≤ 3 by norm_num), Real.sqrt_nonneg 3]