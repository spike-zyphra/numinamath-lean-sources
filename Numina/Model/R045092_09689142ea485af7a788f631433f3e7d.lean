import Mathlib

theorem algebra_225283 (x y z : ℝ) (hx : (x^2 - x + 1) * (4 * y^2 + 6 * y + 4) * (4 * z^2 - 12 * z + 25) = 21) :
    x = 1 / 2 ∧ y = -3 / 4 ∧ z = 3 / 2 := by
  have h1 : x^2 - x + 1 ≥ 3 / 4 := by
    nlinarith [sq_nonneg (x - 1 / 2)]
  have h2 : 4 * y^2 + 6 * y + 4 ≥ 7 / 4 := by
    nlinarith [sq_nonneg (y + 3 / 4)]
  have h3 : 4 * z^2 - 12 * z + 25 ≥ 16 := by
    nlinarith [sq_nonneg (z - 3 / 2)]
  have h4 : (x - 1 / 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y + 3 / 4), sq_nonneg (z - 3 / 2), 
      mul_nonneg (sq_nonneg (x - 1 / 2)) (sq_nonneg (y + 3 / 4)), 
      mul_nonneg (sq_nonneg (x - 1 / 2)) (sq_nonneg (z - 3 / 2)), 
      mul_nonneg (sq_nonneg (y + 3 / 4)) (sq_nonneg (z - 3 / 2))
    ]
  have hx1 : x = 1 / 2 := by
    nlinarith [pow_eq_zero h4]
  have h5 : (y + 3 / 4) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y + 3 / 4), sq_nonneg (z - 3 / 2), 
      mul_nonneg (sq_nonneg (x - 1 / 2)) (sq_nonneg (y + 3 / 4)), 
      mul_nonneg (sq_nonneg (x - 1 / 2)) (sq_nonneg (z - 3 / 2)), 
      mul_nonneg (sq_nonneg (y + 3 / 4)) (sq_nonneg (z - 3 / 2))
    ]
  have hy1 : y = -3 / 4 := by
    nlinarith [pow_eq_zero h5]
  have h6 : (z - 3 / 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y + 3 / 4), sq_nonneg (z - 3 / 2), 
      mul_nonneg (sq_nonneg (x - 1 / 2)) (sq_nonneg (y + 3 / 4)), 
      mul_nonneg (sq_nonneg (x - 1 / 2)) (sq_nonneg (z - 3 / 2)), 
      mul_nonneg (sq_nonneg (y + 3 / 4)) (sq_nonneg (z - 3 / 2))
    ]
  have hz1 : z = 3 / 2 := by
    nlinarith [pow_eq_zero h6]
  exact ⟨hx1, hy1, hz1⟩