import Mathlib

theorem inequalities_165923 (x y z w : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w)
    (h : x^2 + y^2 + z^2 + w^2 = 1) :
    x^2 * y * z * w + x * y^2 * z * w + x * y * z^2 * w + x * y * z * w^2 ≤ 1 / 8 := by 
  have h1 : 0 ≤ x * y * z * w := by positivity
  have h2 : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 1 := h
  have h3 : x * y * z * w ≤ 1 / 16 := by
    nlinarith [sq_nonneg (x * y - z * w), sq_nonneg (x * z - y * w), sq_nonneg (x * w - y * z),
      sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - w), sq_nonneg (y - z), sq_nonneg (y - w), sq_nonneg (z - w),
      mul_pos hx hy, mul_pos hx hz, mul_pos hx hw, mul_pos hy hz, mul_pos hy hw, mul_pos hz hw
    ]
  have h4 : x + y + z + w ≤ 2 := by
    nlinarith [sq_nonneg (x + y + z + w - 2), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - w), sq_nonneg (y - z), sq_nonneg (y - w), sq_nonneg (z - w),
      h, mul_pos hx hy, mul_pos hx hz, mul_pos hx hw, mul_pos hy hz, mul_pos hy hw, mul_pos hz hw
    ]
  have h5 : x ^ 2 * y * z * w + x * y ^ 2 * z * w + x * y * z ^ 2 * w + x * y * z * w ^ 2 = x * y * z * w * (x + y + z + w) := by
    ring
  rw [h5]
  nlinarith [h3, h4, mul_pos hx hy, mul_pos hx hz, mul_pos hx hw, mul_pos hy hz, mul_pos hy hw, mul_pos hz hw, sq_nonneg (x * y * z * w - 1 / 16), sq_nonneg (x + y + z + w - 2)]