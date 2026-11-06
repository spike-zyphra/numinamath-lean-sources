import Mathlib

theorem algebra_178704 {x1 x2 m : ℝ} (hx1 : 3*x1^2+3*m*x1+m^2-1=0) (hx2 : 3*x2^2+3*m*x2+m^2-1=0)
    (hroots : x1≠x2) : 3*x1^6+3*m*x1^3+m^2-1=3*x2^6+3*m*x2^3+m^2-1 := by
  have h1 : 3 * (x1 ^ 2 - x2 ^ 2) + 3 * m * (x1 - x2) = 0 := by
    nlinarith 
  have h2 : x1 + x2 = -m := by
    apply (mul_left_inj' (show x1 - x2 ≠ 0 by
      intro h
      apply hroots
      linarith
    )).mp
    linarith 
  have eq3 : x1 * x2 = (m^2 - 1)/3 := by
    have eq4 : x1 ^ 2 = -m * x1 - (m ^ 2 - 1) / 3 := by 
      nlinarith 
    have eq5 : x2 ^ 2 = -m * x2 - (m ^ 2 - 1) / 3 := by 
      nlinarith 
    nlinarith [sq_pos_of_ne_zero (show (x1 - x2) ≠ 0 by
      intro h0
      apply hroots
      linarith
    ), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2 - (-m))]
  have h4 : x1^3 + x2^3 + m = 0 := by 
    have eq1 : x1^3 + x2^3 = (x1 + x2)^3 - 3 * (x1 * x2) * (x1 + x2) := by 
      ring 
    rw [eq1, h2, eq3]
    nlinarith 
  have eq2 : 3 * x1^6 + 3 * m * x1^3 + m^2 - 1 - (3 * x2^6 + 3 * m * x2^3 + m^2 - 1) = 
    3 * (x1 ^ 3 - x2 ^ 3) * (x1 ^ 3 + x2 ^ 3 + m) := by 
    ring 
  have eq3 : 3 * (x1 ^ 3 - x2 ^ 3) * (x1 ^ 3 + x2 ^ 3 + m) = 0 := by 
    rw [show x1 ^ 3 + x2 ^ 3 + m = 0 by linarith [h4]]
    norm_num 
  have h5 : 3 * x1^6 + 3 * m * x1^3 + m^2 - 1 - (3 * x2^6 + 3 * m * x2^3 + m^2 - 1) = 0 := by 
    linarith [eq2, eq3]
  linarith [h5]