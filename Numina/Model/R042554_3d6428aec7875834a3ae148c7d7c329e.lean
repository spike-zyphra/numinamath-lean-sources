import Mathlib

theorem inequalities_69672 (a b c x y z : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : a + b + c = x + y + z) :
    a ^ 3 / x ^ 2 + b ^ 3 / y ^ 2 + c ^ 3 / z ^ 2 ≥ a + b + c := by 
  have h1 : a ^ 3 / x ^ 2 + b ^ 3 / y ^ 2 + c ^ 3 / z ^ 2 - (a + b + c) ≥ 0 := by
    have h2 : 0 < x ^ 2 := by positivity
    have h3 : 0 < y ^ 2 := by positivity
    have h4 : 0 < z ^ 2 := by positivity
    have h5 : 0 < x ^ 2 * y ^ 2 * z ^ 2 := by positivity
    have h6 : a ^ 3 / x ^ 2 + b ^ 3 / y ^ 2 + c ^ 3 / z ^ 2 - (a + b + c) = 
        (a ^ 3 * y ^ 2 * z ^ 2 + b ^ 3 * x ^ 2 * z ^ 2 + c ^ 3 * x ^ 2 * y ^ 2 - (a + b + c) * x ^ 2 * y ^ 2 * z ^ 2) / (x ^ 2 * y ^ 2 * z ^ 2) := by
      field_simp
      ring
    rw [h6]
    have eq1 : a + b + c = x + y + z := h
    have eq2 : a ^ 3 * y ^ 2 * z ^ 2 + b ^ 3 * x ^ 2 * z ^ 2 + c ^ 3 * x ^ 2 * y ^ 2 ≥ (a + b + c) * x ^ 2 * y ^ 2 * z ^ 2 := by 
      have eq1 : a + b + c = x + y + z := h 
      have hx2 : x ^ 2 > 0 := by positivity
      have hy2 : y ^ 2 > 0 := by positivity
      have hz2 : z ^ 2 > 0 := by positivity
      nlinarith [sq_nonneg (a - x), sq_nonneg (b - y), sq_nonneg (c - z), 
        sq_nonneg (a * y - b * x), sq_nonneg (b * x - a * y), 
        sq_nonneg (a * z - c * x), sq_nonneg (b * z - c * y), 
        sq_nonneg (a * y * z - x * y * z), 
        sq_nonneg (b * x * z - x * y * z), 
        sq_nonneg (c * x * y - x * y * z), 
        mul_nonneg ha (show 0 ≤ b by linarith), 
        mul_nonneg ha (show 0 ≤ c by linarith), 
        mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith), 
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
        ]
    apply div_nonneg 
    linarith [eq2]
    positivity 
  linarith