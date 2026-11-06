import Mathlib

open Real

theorem algebra_162551 : (cos (7 * π / 24))^4 + (sin (11 * π / 24))^4 + (sin (17 * π / 24))^4 + (cos (13 * π / 24))^4 = 3 / 2 := by
  have h1 : sin (17 * π / 24) = sin (7 * π / 24) := by
    have h2 : 17 * π / 24 = Real.pi - 7 * π / 24 := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [sin_pi_sub]
  have h2 : cos (13 * π / 24) = - cos (11 * π / 24) := by
    have h3 : 13 * π / 24 = Real.pi - 11 * π / 24 := by
      linarith [Real.pi_pos]
    rw [h3]
    rw [cos_pi_sub]
  rw [h1, h2]
  have h3 : (cos (7 * π / 24))^4 + (sin (11 * π / 24))^4 + (sin (7 * π / 24))^4 + (cos (11 * π / 24))^4 = 3 / 2 := by
    have h4 : (cos (7 * π / 24))^4 + (sin (7 * π / 24))^4 = 1 - 2 * ((cos (7 * π / 24)) ^ 2 * (sin (7 * π / 24)) ^ 2) := by
      have h5 : (cos (7 * π / 24))^4 + (sin (7 * π / 24))^4 = ((cos (7 * π / 24))^2 + (sin (7 * π / 24))^2) ^ 2 - 2 * ((cos (7 * π / 24))^2 * (sin (7 * π / 24))^2) := by
        ring
      have h6 : (cos (7 * π / 24))^2 + (sin (7 * π / 24))^2 = 1 := by
        exact Real.cos_sq_add_sin_sq (7 * π / 24)
      rw [h5, h6]
      all_goals norm_num
    have h5 : (sin (11 * π / 24))^4 + (cos (11 * π / 24))^4 = 1 - 2 * ((sin (11 * π / 24))^2 * (cos (11 * π / 24))^2) := by
      have h6 : (sin (11 * π / 24))^4 + (cos (11 * π / 24))^4 = ((sin (11 * π / 24))^2 + (cos (11 * π / 24))^2) ^ 2 - 2 * ((sin (11 * π / 24))^2 * (cos (11 * π / 24))^2) := by
        ring
      have h7 : (sin (11 * π / 24))^2 + (cos (11 * π / 24))^2 = 1 := by
        have h8 : (cos (11 * π / 24))^2 + (sin (11 * π / 24))^2 = 1 := by
          exact Real.cos_sq_add_sin_sq (11 * π / 24)
        linarith
      rw [h6, h7]
      all_goals norm_num
    have h6 : (cos (7 * π / 24))^4 + (sin (11 * π / 24))^4 + (sin (7 * π / 24))^4 + (cos (11 * π / 24))^4 =
        ((cos (7 * π / 24))^4 + (sin (7 * π / 24))^4) + ((sin (11 * π / 24))^4 + (cos (11 * π / 24))^4) := by ring
    rw [h6, h4, h5]
    have h7 : (cos (7 * π / 24)) ^ 2 * (sin (7 * π / 24)) ^ 2 + (sin (11 * π / 24)) ^ 2 * (cos (11 * π / 24)) ^ 2 = 1 / 4 := by
      have h8 : (cos (7 * π / 24)) ^ 2 * (sin (7 * π / 24)) ^ 2 = (1 / 4) * (sin (7 * π / 12))^2 := by
        have h9 : sin (7 * π / 12) = 2 * sin (7 * π / 24) * cos (7 * π / 24) := by
          have h10 : 7 * π / 12 = 2 * (7 * π / 24) := by ring
          rw [h10]
          rw [sin_two_mul]
        rw [h9]
        ring_nf
      have h9 : (sin (11 * π / 24)) ^ 2 * (cos (11 * π / 24)) ^ 2 = (1 / 4) * (sin (11 * π / 12))^2 := by
        have h10 : sin (11 * π / 12) = 2 * sin (11 * π / 24) * cos (11 * π / 24) := by
          have h11 : 11 * π / 12 = 2 * (11 * π / 24) := by ring
          rw [h11]
          rw [sin_two_mul]
        rw [h10]
        ring_nf
      rw [h8, h9]
      have h15 : sin (11 * π / 12) = sin (π / 12) := by
        have h16 : 11 * π / 12 = Real.pi - (π / 12) := by ring
        rw [h16]
        rw [sin_pi_sub]
      have h18 : sin (7 * π / 12) = cos (π / 12) := by
        have h17 : 7 * π / 12 = Real.pi / 2 + (π / 12) := by ring
        rw [h17]
        have h18 : sin (Real.pi / 2 + (π / 12)) = cos (π / 12) := by
          rw [sin_add, sin_pi_div_two, cos_pi_div_two]
          ring
        exact h18
      rw [h15, h18]
      have h16 : (cos (π / 12))^2 + (sin (π / 12))^2 = 1 := by
        exact Real.cos_sq_add_sin_sq (π / 12)
      nlinarith
    nlinarith
  nlinarith