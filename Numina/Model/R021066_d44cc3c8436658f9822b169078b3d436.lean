import Mathlib

theorem algebra_311846 {x y z : ℝ} (hx : x ≠ y) (hy : y ≠ z) (hz : x ≠ z)
    (h : x + y + z = x * y * z) (h1 : x * y * z ≠ 0) :
    ((1 - y ^ 2) * (1 - z ^ 2)) / (y * z) + ((1 - z ^ 2) * (1 - x ^ 2)) / (z * x) +
    ((1 - x ^ 2) * (1 - y ^ 2)) / (x * y) = 4 := by

  have h2 : x ≠ 0 := by
    by_contra h3
    have h4 : x * y * z = 0 := by
      rw [h3]
      norm_num
    contradiction

  have h3 : y ≠ 0 := by
    by_contra h4
    have h5 : x * y * z = 0 := by
      rw [h4]
      norm_num
    contradiction

  have h4 : z ≠ 0 := by
    by_contra h5
    have h6 : x * y * z = 0 := by
      rw [h5]
      norm_num
    contradiction

  have eq1 : ((1 - y ^ 2) * (1 - z ^ 2)) / (y * z) + ((1 - z ^ 2) * (1 - x ^ 2)) / (z * x) + ((1 - x ^ 2) * (1 - y ^ 2)) / (x * y) =
      (x * (1 - y^2) * (1 - z^2) + y * (1 - z^2) * (1 - x^2) + z * (1 - x^2) * (1 - y^2)) / (x * y * z) := by
    field_simp [show y * z ≠ 0 by
      apply mul_ne_zero
      exact h3
      exact h4, show z * x ≠ 0 by
      apply mul_ne_zero
      exact h4
      exact h2, show x * y ≠ 0 by
      apply mul_ne_zero
      exact h2
      exact h3]
    ring

  rw [eq1]

  have eq2 : x * (1 - y^2) * (1 - z^2) + y * (1 - z^2) * (1 - x^2) + z * (1 - x^2) * (1 - y^2) = 4 * (x * y * z) := by
    nlinarith [sq_pos_of_ne_zero h1, sq_pos_of_ne_zero (show (y) ≠ 0 by assumption), 
            sq_pos_of_ne_zero (show (z) ≠ 0 by assumption), 
            sq_pos_of_ne_zero (show (x) ≠ 0 by assumption), 
            sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
            sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
            h, 
            sq_nonneg (x + y + z - x * y * z)
        ]

  rw [eq2]

  have eq3 : (4 * (x * y * z) ) / (x * y * z) = 4 := by
    field_simp [show x * y * z ≠ 0 by assumption]

  linarith [eq3]