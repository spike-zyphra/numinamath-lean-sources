import Mathlib

theorem inequalities_175224 (x a : ℝ) (ha : 0 < a) (hx : 0 < x) (h : x < a) :
    (a - x)^6 - 3 * a * (a - x)^5 + (5 / 2) * a^2 * (a - x)^4 - (1 / 2) * a^4 * (a - x)^2 < 0 := by
  have h1 : 0 < a - x := by
    nlinarith
  have h2 : 0 < x := by linarith
  have h3 : 0 < a := by linarith
  nlinarith [sq_pos_of_pos h1, sq_pos_of_pos h2, sq_pos_of_pos h3,
          sq_nonneg (a - x - x), sq_nonneg (a - 2 * x), sq_nonneg (a ^ 2 - (a - x) ^ 2),
          sq_nonneg ((a - x) ^ 2 - x ^ 2), sq_nonneg ((a - x) * x),
          sq_nonneg ((a - x) - x), sq_nonneg (a - 2 * x), sq_nonneg (a - x - a / 2), sq_nonneg (x - a / 2), 
          mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3,
          mul_pos (show 0 < x by linarith) (show 0 < a - x by nlinarith),
          pow_pos h1 3, pow_pos h1 4, pow_pos h1 5, pow_pos h1 6,
          pow_pos h2 3, pow_pos h2 4, pow_pos h2 5, pow_pos h2 6,
          pow_pos h3 3, pow_pos h3 4, pow_pos h3 5, pow_pos h3 6,
          mul_pos (pow_pos h1 2) (pow_pos h2 2), 
          mul_pos (pow_pos h1 2) (pow_pos h3 2), 
          mul_pos (pow_pos h2 2) (pow_pos h3 2)
]