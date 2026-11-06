import Mathlib

theorem algebra_7867 {P Q : ℝ → ℝ} (hP : P = fun x => x^3 + x^2 - 1)
    (hQ : Q = fun x => x^3 - x - 1) (r s : ℝ) (hr : r ≠ s) (hP1 : P r = 0)
    (hP2 : P s = 0) : Q (r * s) = 0 := by
  have hr1 : r^3 + r^2 - 1 = 0 := by 
    rw [hP] at hP1
    simpa using hP1
  have hs1 : s^3 + s^2 - 1 = 0 := by 
    rw [hP] at hP2
    simpa using hP2
  have h3 : r^3 + r^2 - (s^3 + s^2) = 0 := by
    linarith
  have h4 : (r - s) * (r^2 + r * s + s^2 + r + s) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show (r - s) ≠ 0 by 
      intro h'
      apply hr
      linarith
    ), sq_nonneg (r - s), sq_nonneg (r + s), sq_nonneg (r * s)]
  have h5 : r^2 + r * s + s^2 + r + s = 0 := by
    apply (mul_left_inj' (show r - s ≠ 0 by 
      intro h'
      apply hr
      linarith
    )).mp
    linarith
  have h6 : (r * s) ^ 3 - (r * s) - 1 = 0 := by
    nlinarith [sq_pos_of_ne_zero (show (r - s) ≠ 0 by 
      intro h'
      apply hr
      linarith
    ), sq_nonneg (r^2 - s^2), sq_nonneg (r^3 - s^3), sq_nonneg (r * s - 1), sq_nonneg (r + s), sq_nonneg (r - s), sq_nonneg (r * s^2 + s * r^2)]
  rw [hQ]
  simpa using h6