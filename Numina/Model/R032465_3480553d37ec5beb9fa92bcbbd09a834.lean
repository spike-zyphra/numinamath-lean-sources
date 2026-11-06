import Mathlib

open Real

theorem algebra_164450 : (sin (π / 8))^4 + (cos (3 * π / 8))^4 + (sin (5 * π / 8))^4 + (cos (7 * π / 8))^4 = 3 / 2 := by
  have h1 : sin (5 * π / 8) = sin (3 * π / 8) := by
    have h2 : 5 * π / 8 = π - 3 * π / 8 := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [show sin (π - 3 * π / 8) = sin (3 * π / 8) by
      rw [sin_pi_sub]
    ]
  have h3 : cos (7 * π / 8) = -cos (π / 8) := by
    have h4 : 7 * π / 8 = π - π / 8 := by
      linarith [Real.pi_pos]
    rw [h4]
    rw [show cos (π - π / 8) = -cos (π / 8) by
      rw [cos_pi_sub]
    ]
  have h4 : cos (3 * π / 8) = sin (π / 8) := by
    have h5 : 3 * π / 8 = π / 2 - π / 8 := by
      linarith [Real.pi_pos]
    rw [h5]
    rw [show cos (π / 2 - π / 8) = sin (π / 8) by
      rw [cos_pi_div_two_sub]
    ]
  have h5 : (sin (5 * π / 8))^4 = (sin (3 * π / 8))^4 := by
    rw [h1]
  have h6 : (cos (7 * π / 8))^4 = (cos (π / 8))^4 := by
    rw [h3]
    ring
  have h7 : (cos (3 * π / 8))^4 = (sin (π / 8))^4 := by
    rw [h4]
  have h8 : sin (3 * π / 8) = cos (π / 8) := by
    have h9 : 3 * π / 8 = π / 2 - π / 8 := by
      linarith [Real.pi_pos]
    rw [h9]
    rw [show sin (π / 2 - π / 8) = cos (π / 8) by
      rw [sin_pi_div_two_sub]
    ]
  have h9 : (sin (3 * π / 8))^4 = (cos (π / 8))^4 := by
    rw [h8]
  have h10 : (sin (π / 8))^4 + (cos (3 * π / 8))^4 + (sin (5 * π / 8))^4 + (cos (7 * π / 8))^4 =
    2 * ( (sin (π / 8))^4 + (cos (π / 8))^4 ) := by
    rw [h5, h6, h7, h9]
    ring
  rw [h10]
  have h11 : (sin (π / 8))^4 + (cos (π / 8))^4 = 3 / 4 := by
    have h12 : (sin (π / 8))^2 + (cos (π / 8))^2 = 1 := by
      exact Real.sin_sq_add_cos_sq (π / 8)
    have h13 : (sin (π / 8))^4 + (cos (π / 8))^4 = ((sin (π / 8))^2 + (cos (π / 8))^2)^2 - 2 * ((sin (π / 8)) * (cos (π / 8)))^2 := by
      nlinarith
    rw [h13, h12]
    have h14 : sin (π / 4) = Real.sqrt 2 / 2 := by
      have h15 : sin (π / 4) = Real.sqrt 2 / 2 := by
        exact Real.sin_pi_div_four
      linarith
    have h15 : (sin (π / 8) * cos (π / 8)) = Real.sqrt 2 / 4 := by
      have h16 : sin (2 * (π / 8)) = 2 * sin (π / 8) * cos (π / 8) := by
        rw [sin_two_mul]
      have h17 : 2 * (π / 8) = π / 4 := by
        ring
      have h18 : sin (2 * (π / 8)) = sin (π / 4) := by
        rw [h17]
      have h19 : sin (π / 4) = Real.sqrt 2 / 2 := by
        exact Real.sin_pi_div_four
      nlinarith
    rw [h15]
    nlinarith [Real.sqrt_pos.mpr Real.pi_pos, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  nlinarith [h11]