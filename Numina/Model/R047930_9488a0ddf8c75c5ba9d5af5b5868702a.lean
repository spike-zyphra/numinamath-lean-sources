import Mathlib

theorem algebra_298392 {a b : ℝ} (ha : a^2 + 2 * a - 5 = 0) (hb : b^2 + 2 * b - 5 = 0) (hab : a ≠ b) :
    a^2 * b + a * b^2 = 10 := by

  have h1 : a + b = -2 := by 
    have h2 : a^2 - b^2 + 2 * (a - b) = 0 := by
      nlinarith
    have h3 : a - b ≠ 0 := by
      intro h
      apply hab
      linarith
    have h4 : a + b + 2 = 0 := by
      apply (mul_left_inj' h3).mp
      linarith
    linarith

  have h2 : a * b = -5 := by
    have h3 : a^2 + b^2 = 14 := by
      have h4 : a^2 = 5 - 2 * a := by
        linarith
      have h5 : b^2 = 5 - 2 * b := by
        linarith
      nlinarith
    nlinarith [ sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      intro h
      apply hab
      linarith
    ), h1 ]
  
  have h3 : a^2 * b + a * b^2 = a * b * (a + b) := by
    ring

  rw [h3, h2, h1]
  all_goals norm_num