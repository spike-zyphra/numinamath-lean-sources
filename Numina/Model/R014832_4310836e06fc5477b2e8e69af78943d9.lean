import Mathlib

theorem inequalities_597116 (a b c : ℝ) (x y z : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : a + b + c = x + y + z) :
    a^3 / x^2 + b^3 / y^2 + c^3 / z^2 ≥ a + b + c := by

  have hx4 : 0 < x ^ 2 * y ^ 2 * z ^ 2 := by positivity
  have hx3 : a^3 / x^2 + b^3 / y^2 + c^3 / z^2 - (a + b + c) >= 0 := by
    have h1 : 0 < x ^ 2 * y ^ 2 * z ^ 2 := by positivity
    have h44 : a ^ 3 * y ^ 2 * z ^ 2 + b ^ 3 * x ^ 2 * z ^ 2 + c^ 3 * x ^ 2 * y ^ 2 >= (a + b + c) * x ^ 2 * y ^ 2 * z ^ 2 := by
      nlinarith [sq_nonneg (a * y * z - x * y * z), sq_nonneg (b * x * z - y * x * z), sq_nonneg (c * x * y - z * x * y), 
           sq_nonneg (a - x), sq_nonneg (b - y), sq_nonneg (c - z), 
           sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
           sq_nonneg (a * (a - x) ), sq_nonneg (b * (b - y) ), sq_nonneg (c * (c - z) ), 
           mul_nonneg ha (show 0 ≤ (x ^ 2 * y ^ 2 * z ^ 2 ) by positivity), 
           mul_nonneg ha (show 0 ≤ (y ^ 2 ) by positivity), 
           mul_nonneg ha (show 0 ≤ z ^ 2 by positivity), 
           mul_nonneg hb (show 0 ≤ (x ^ 2 * y ^ 2 * z ^ 2 ) by positivity), 
           mul_nonneg hb (show 0 ≤ (x ^ 2 ) by positivity), 
           mul_nonneg hb (show 0 ≤ z ^ 2 by positivity), 
           mul_nonneg hc (show 0 ≤ (x ^ 2 * y ^ 2 * z ^ 2 ) by positivity), 
           mul_nonneg hc (show 0 ≤ (x ^ 2 ) by positivity), 
           mul_nonneg hc (show 0 ≤ y ^ 2 by positivity), 
           mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
           mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
           mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith), 
           mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith), 
           h
        ]
    have hxy : a^3 / x^2 + b^3 / y^2 + c^3 / z^2 - (a + b + c) =
      (a^3 * y^ 2 * z^ 2 + b^ 3 * x^ 2 * z^ 2 + c^ 3 * x^ 2 * y^ 2 - (a + b + c) * x^ 2 * y^ 2 * z^ 2) / (x^2 * y^2 * z^2) := by 
      field_simp
      ring
    rw [hxy] at *
    apply div_nonneg
    linarith
    all_goals positivity
  linarith