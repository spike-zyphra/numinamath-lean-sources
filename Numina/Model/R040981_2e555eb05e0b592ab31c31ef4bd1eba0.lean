import Mathlib

theorem inequalities_213222 (x y z : ℝ) :
    abs x < abs (y - z) ∧ abs y < abs (z - x) ∧ abs z < abs (x - y) → False := by
  intro h
  rcases h with ⟨h1, h2, h3⟩
  have h4 : x ^ 2 < (y - z) ^ 2 := by
    apply sq_lt_sq.mpr
    exact h1
  have h5 : x^2 < y^2 - 2 * y * z + z^2 := by 
    nlinarith [h4]
  have h7 : y ^ 2 < (z - x) ^ 2 := by 
    apply sq_lt_sq.mpr
    exact h2
  have h8 : y^2 < z^2 - 2 * z * x + x^2 := by 
    nlinarith [h7]
  have h10 : z ^ 2 < (x - y) ^ 2 := by 
    apply sq_lt_sq.mpr
    exact h3
  have h11 : z^2 < x^2 - 2 * x * y + y^2 := by 
    nlinarith [h10]
  have h12 : x + y + z < 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      h5, h8, h11, 
      sq_nonneg (x + y + z), 
      sq_nonneg (x - (y + z)), 
      sq_nonneg (y - (x + z)), 
      sq_nonneg (z - (x + y))
      ]
  have h13 : x + y + z > 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      h5, h8, h11, 
      sq_nonneg (x + y + z), 
      sq_nonneg (x - (y + z)), 
      sq_nonneg (y - (x + z)), 
      sq_nonneg (z - (x + y))
      ]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    h5, h8, h11, 
    sq_nonneg (x + y + z), 
    sq_nonneg (x - (y + z)), 
    sq_nonneg (y - (x + z)), 
    sq_nonneg (z - (x + y)), 
    h12, 
    h13
    ]