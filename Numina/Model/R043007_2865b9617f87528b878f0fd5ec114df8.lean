import Mathlib

theorem algebra_151972 {x y z : ℝ} (h1 : x^2 + y^2 + z^2 = 9 / 4) (h2 : -8 * x + 6 * y - 24 * z = 39) :
    x = -6 / 13 ∧ y = 9 / 26 ∧ z = -18 / 13 := by 
  have h3 : (x + 6 / 13) ^ 2 + (y - 9 / 26) ^ 2 + (z + 18 / 13) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x + 6 / 13), sq_nonneg (y - 9 / 26), sq_nonneg (z + 18 / 13),
      sq_nonneg (x - (-6 / 13)), sq_nonneg (y - 9 / 26), sq_nonneg (z - (-18 / 13))
    ]
  have hx1 : x + 6 / 13 = 0 := by
    nlinarith [sq_nonneg (x + 6 / 13), sq_nonneg (y - 9 / 26), sq_nonneg (z + 18 / 13), h3
    ]
  have hy1 : y - 9 / 26 = 0 := by
    nlinarith [sq_nonneg (x + 6 / 13), sq_nonneg (y - 9 / 26), sq_nonneg (z + 18 / 13), h3
    ]
  have hz1 : z + 18 / 13 = 0 := by
    nlinarith [sq_nonneg (x + 6 / 13), sq_nonneg (y - 9 / 26), sq_nonneg (z + 18 / 13), h3
    ]
  constructor
  · -- Prove x = -6/13
    linarith
  constructor
  · -- Prove y = 9/26
    linarith
  · -- Prove z = -18/13
    linarith