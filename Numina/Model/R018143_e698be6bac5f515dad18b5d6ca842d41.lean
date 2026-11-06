import Mathlib

open Real

theorem algebra_162076 : (cos (5 * π / 24))^4 + (cos (11 * π / 24))^4 +
    (sin (19 * π / 24))^4 + (sin (13 * π / 24))^4 = 3 / 2 := by 
  have h1 : sin (19 * π / 24) = sin (5 * π / 24) := by 
    have h1 : 19 * π / 24 = π - (5 * π / 24) := by 
      linarith [Real.pi_pos]
    rw [h1]
    rw [sin_pi_sub]
  have h2 : sin (13 * π / 24) = sin (11 * π / 24) := by 
    have h2 : 13 * π / 24 = π - (11 * π / 24) := by 
      linarith [Real.pi_pos]
    rw [h2]
    rw [sin_pi_sub]
  rw [h1, h2]
  have h3 : (cos (5 * π / 24))^4 + (sin (5 * π / 24))^4 = 1 - (1 / 2) * (sin (2 * (5 * π / 24))) ^ 2 := by 
    have h4 : (cos (5 * π / 24))^4 + (sin (5 * π / 24))^4 = 
        ((cos (5 * π / 24)) ^ 2 + (sin (5 * π / 24)) ^ 2) ^ 2 - 2 * ((cos (5 * π / 24)) * (sin (5 * π / 24)) ) ^ 2 := by 
      ring 
    have h5 : (cos (5 * π / 24)) ^ 2 + (sin (5 * π / 24)) ^ 2 = 1 := by 
      exact Real.cos_sq_add_sin_sq (5 * π / 24)
    have h6 : (cos (5 * π / 24)) * (sin (5 * π / 24)) = (1 / 2) * sin (2 * (5 * π / 24)) := by 
      have h7 : sin (2 * (5 * π / 24)) = 2 * sin (5 * π / 24) * cos (5 * π / 24) := by 
        rw [sin_two_mul]
      linarith 
    rw [h4, h5, h6]
    linarith 
  have h4 : (cos (11 * π / 24))^4 + (sin (11 * π / 24))^4 = 1 - (1 / 2) * (sin (2 * (11 * π / 24))) ^ 2 := by 
    have h4 : (cos (11 * π / 24))^4 + (sin (11 * π / 24))^4 = 
        ((cos (11 * π / 24))  ^ 2 + (sin (11 * π / 24)) ^ 2) ^ 2 - 2 * ((cos (11 * π / 24)) * (sin (11 * π / 24)) ) ^ 2 := by 
      ring 
    have h5 : (cos (11 * π / 24)) ^ 2 + (sin (11 * π / 24)) ^ 2 = 1 := by 
      exact Real.cos_sq_add_sin_sq (11 * π / 24)
    have h6 : (cos (11 * π / 24)) * (sin (11 * π / 24)) = (1 / 2) * sin (2 * (11 * π / 24)) := by 
      have h7 : sin (2 * (11 * π / 24)) = 2 * sin (11 * π / 24) * cos (11 * π / 24) := by 
        rw [sin_two_mul]
      linarith 
    rw [h4, h5, h6]
    linarith 
  have h6 : sin (2 * (5 * π / 24)) = sin (5 * π / 12) := by 
    ring_nf 
  have h7 : (sin (5 * π / 12)) ^ 2 + (sin (2 * (11 * π / 24))) ^ 2 = 1 := by 
    have h8 : sin (2 * (11 * π / 24)) = sin (11 * π / 12) := by 
      ring_nf 
    rw [h8]
    have h8 : sin (11 * π / 12) = sin (Real.pi - (Real.pi / 12)) := by 
      ring_nf 
    have h9 : sin (Real.pi - (Real.pi / 12)) = sin (Real.pi / 12) := by 
      rw [sin_pi_sub] 
    rw [h8, h9]
    have h10 : sin (5 * π / 12) = cos (Real.pi / 12) := by 
      have h11 : 5 * π / 12 = Real.pi / 2 - Real.pi / 12 := by 
        linarith [Real.pi_pos]
      rw [h11] 
      rw [sin_pi_div_two_sub] 
    rw [h10]
    have h11 : (cos (Real.pi / 12)) ^ 2 + (sin (Real.pi / 12)) ^ 2 = 1 := by 
      exact Real.cos_sq_add_sin_sq (Real.pi / 12)
    nlinarith 
  rw [show (cos (5 * π / 24)) ^ 4 + (cos (11 * π / 24)) ^ 4 + (sin (5 * π / 24)) ^ 4 + (sin (11 * π / 24)) ^ 4 = 
      ((cos (5 * π / 24)) ^ 4 + (sin (5 * π / 24)) ^ 4) + ((cos (11 * π / 24)) ^ 4 + (sin (11 * π / 24)) ^ 4) by ring]
  rw [h3, h4]
  have h8 : (1 - (1 / 2) * (sin (2 * (5 * π / 24))) ^ 2 : ℝ) + (1 - (1 / 2) * (sin (2 * (11 * π / 24))) ^ 2 : ℝ) = 3 / 2 := by 
    rw [show sin (2 * (5 * π / 24)) = sin (5 * π / 12) by ring_nf] 
    have h9 : (sin (5 * π / 12)) ^ 2 + (sin (2 * (11 * π / 24))) ^ 2 = 1 := by 
      have h8 : sin (2 * (11 * π / 24)) = sin (11 * π / 12) := by 
        ring_nf 
      rw [h8]
      have h8 : sin (11 * π / 12) = sin (Real.pi - (Real.pi / 12)) := by 
        ring_nf 
      have h9 : sin (Real.pi - (Real.pi / 12)) = sin (Real.pi / 12) := by 
        rw [sin_pi_sub] 
      rw [h8, h9]
      have h10 : sin (5 * π / 12) = cos (Real.pi / 12) := by 
        have h11 : 5 * π / 12 = Real.pi / 2 - Real.pi / 12  := by 
          linarith [Real.pi_pos] 
        rw [h11] 
        rw [sin_pi_div_two_sub]
      rw [h10]
      have h11 : (cos (Real.pi / 12)) ^ 2 + (sin (Real.pi / 12)) ^ 2 = 1 := by 
        exact Real.cos_sq_add_sin_sq (Real.pi / 12)
      nlinarith 
    nlinarith 
  linarith