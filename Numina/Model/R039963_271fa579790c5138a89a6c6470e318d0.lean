import Mathlib

theorem algebra_132858 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x * y + y * z + z * x = 12) (h2 : x * y * z = 2 + x + y + z) :
    x = 2 ∧ y = 2 ∧ z = 2 := by
  have h3 : x = 2 := by
    nlinarith [sq_nonneg (x * (y - z)), sq_nonneg (y * (x - z)), sq_nonneg (z * (x - y)), 
      sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
    ]
  have h4 : y = 2 := by 
    nlinarith [sq_nonneg (x * (y - z)), sq_nonneg (y * (x - z)), sq_nonneg (z * (x - y)), 
      sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
    ]
  have h5 : z = 2 := by
    nlinarith [sq_nonneg (x * (y - z)), sq_nonneg (y * (x - z)), sq_nonneg (z * (x - y)), 
      sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
    ]
  exact ⟨h3, h4, h5⟩