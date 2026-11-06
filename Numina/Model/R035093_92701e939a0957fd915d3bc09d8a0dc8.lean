import Mathlib

theorem algebra_4769 {x y z : ℝ} (hx1 : (x^2 + 3)^4 = 256 * (2 * y - 1)) (hy1 : (y^2 + 3)^4 = 256 * (2 * z - 1)) (hz1 : (z^2 + 3)^4 = 256 * (2 * x - 1)) : (x, y, z) = (1, 1, 1) := by
  have h1 : x^2 + 3 ≥ 0 := by nlinarith
  have h2 : y^2 + 3 ≥ 0 := by nlinarith
  have h3 : z^2 + 3 ≥ 0 := by nlinarith
  have h4 : x ≥ 1 / 2 := by
    nlinarith [sq_nonneg (x ^ 2 + 3), sq_nonneg (y - 1), sq_nonneg (z - 1), 
      sq_nonneg (x - 1), sq_nonneg (y ^ 2 + 3), sq_nonneg (z ^ 2 + 3), 
        hx1, hy1, hz1 
    ]
  have h5 : y ≥ 1 / 2 := by
    nlinarith [sq_nonneg (y ^ 2 + 3), sq_nonneg (x - 1), sq_nonneg (z - 1), 
      sq_nonneg (y - 1), sq_nonneg (x ^ 2 + 3), sq_nonneg (z ^ 2 + 3), 
        hx1, hy1, hz1 
    ]
  have h6 : z ≥ 1 / 2 := by
    nlinarith [sq_nonneg (z ^ 2 + 3), sq_nonneg (x - 1), sq_nonneg (y - 1), 
      sq_nonneg (z - 1), sq_nonneg (y ^ 2 + 3), sq_nonneg (x ^ 2 + 3), 
        hx1, hy1, hz1 
    ]
  have h7 : (x - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x^2 + 3 - 4), sq_nonneg (y^2 + 3 - 4), sq_nonneg (z^2 + 3 - 4), 
      sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
        hx1, hy1, hz1
    ]
  have hx2 : x = 1 := by
    nlinarith [h7]
  have h8 : (y - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x^2 + 3 - 4), sq_nonneg (y^2 + 3 - 4), sq_nonneg (z^2 + 3 - 4), 
      sq_nonneg (y - 1), sq_nonneg (z - 1), sq_nonneg (x - 1), 
        hx1, hy1, hz1
    ]
  have hy2 : y = 1 := by
    nlinarith [h8]
  have h9 : (z - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x^2 + 3 - 4), sq_nonneg (y^2 + 3 - 4), sq_nonneg (z^2 + 3 - 4), 
      sq_nonneg (z - 1), sq_nonneg (x - 1), sq_nonneg (y - 1), 
        hx1, hy1, hz1
    ]
  have hz2 : z = 1 := by
    nlinarith [h9]
  simp [Prod.ext_iff, hx2, hy2, hz2]