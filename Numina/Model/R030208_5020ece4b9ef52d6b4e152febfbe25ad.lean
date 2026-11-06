import Mathlib

theorem algebra_164150 : Real.sin (Real.pi / 18) * Real.sin (Real.pi / 6) * Real.sin (5 * Real.pi / 18) * Real.sin (7 * Real.pi / 18) = 1 / 16 := by
  have h1 : Real.sin (5 * Real.pi / 18) * Real.sin (7 * Real.pi / 18) = Real.sin (Real.pi / 3)^2 - Real.sin (Real.pi / 18)^2 := by
    have h2 : 5 * Real.pi / 18 = Real.pi / 3 - Real.pi / 18 := by
      ring_nf
    have h3 : 7 * Real.pi / 18 = Real.pi / 3 + Real.pi / 18 := by
      ring_nf
    rw [h2, h3]
    have h4 : Real.sin (Real.pi / 3 - Real.pi / 18) * Real.sin (Real.pi / 3 + Real.pi / 18) = Real.sin (Real.pi / 3)^2 - Real.sin (Real.pi / 18)^2 := by
      rw [Real.sin_sub, Real.sin_add]
      ring_nf
      <;> simp [Real.sin_sq, Real.cos_sq]
      <;> ring_nf <;> simp [Real.sin_sq]
      <;> ring
    exact h4
  have h2 : Real.sin (Real.pi / 6) = 1 / 2 := by
    exact Real.sin_pi_div_six
  have h3 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
    exact Real.sin_pi_div_three
  have h4 : Real.sin (Real.pi / 3) ^ 2 = 3 / 4 := by
    rw [h3]
    have h5 : (Real.sqrt 3 / 2) ^ 2 = (Real.sqrt 3) ^ 2 / 4 := by
      ring_nf
    rw [h5]
    have h6 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [h6]
    <;> norm_num
  have h5 : Real.sin (Real.pi / 18) * Real.sin (Real.pi / 6) * Real.sin (5 * Real.pi / 18) * Real.sin (7 * Real.pi / 18) = Real.sin (Real.pi / 18) * Real.sin (Real.pi / 6) * (Real.sin (5 * Real.pi / 18) * Real.sin (7 * Real.pi / 18)) := by
    ring_nf
  rw [h5, h1, h2, h4]
  have h7 : Real.sin (3 * (Real.pi / 18)) = 3 * Real.sin (Real.pi / 18) - 4 * Real.sin (Real.pi / 18) ^ 3 := by
    rw [show 3 * (Real.pi / 18) = 3 * (Real.pi / 18) by ring]
    rw [Real.sin_three_mul]
  have h8 : Real.sin (3 * (Real.pi / 18)) = 1 / 2 := by
    have h9 : 3 * (Real.pi / 18) = Real.pi / 6 := by
      ring_nf
      <;> ring_nf <;> nlinarith [Real.pi_pos]
    rw [h9]
    all_goals
      exact Real.sin_pi_div_six
  have h9 : 8 * Real.sin (Real.pi / 18) ^ 3 - 6 * Real.sin (Real.pi / 18) + 1 = 0 := by
    nlinarith [h7, h8]
  nlinarith [sq_nonneg (Real.sin (Real.pi / 18) ^ 2 - 1 / 4), sq_nonneg (Real.sin (Real.pi / 18) - 1 / 2), sq_nonneg (Real.sin (Real.pi / 18) + 1 / 2), Real.sin_pos_of_pos_of_lt_pi (show 0 < Real.pi / 18 by linarith [Real.pi_pos] ) (show Real.pi / 18 < Real.pi by linarith [Real.pi_pos] ) ]
  <;> nlinarith
  all_goals
    nlinarith
    all_goals
      linarith