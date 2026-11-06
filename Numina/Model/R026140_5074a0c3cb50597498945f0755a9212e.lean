import Mathlib

theorem algebra_320150 (x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z = (14 - x) * (14 - y) * (14 - z)) (h1 : x + y + z < 28) :
    x ^ 2 + y ^ 2 + z ^ 2 ≤ 219 := by

  have h2 : x ≤ 13 := by
    nlinarith [sq_nonneg (x - 14), sq_nonneg (y - 14), sq_nonneg (z - 14), 
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, h, h1
      ]

  have h3 : y ≤ 13 := by
    nlinarith [sq_nonneg (x - 14), sq_nonneg (y - 14), sq_nonneg (z - 14), 
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, h, h1
      ]

  have h4 : z ≤ 13 := by
    nlinarith [sq_nonneg (x - 14), sq_nonneg (y - 14), sq_nonneg (z - 14), 
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, h, h1
      ]

  interval_cases x <;> interval_cases y <;> interval_cases z 
    <;> omega