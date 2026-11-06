import Mathlib


lemma lemma_1 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxyz : x * y * z = 1) :
    x + y + z ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
           sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
           mul_pos hx hy, mul_pos hy hz, mul_pos hx hz
         ]


theorem algebra_607923 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a ≤ a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 := by
  have h1 : 0 < a / b := by positivity
  have h2 : 0 < b / c := by positivity
  have h3 : 0 < c / a := by positivity
  have h4 : (a / b) * (b / c) * (c / a) = 1 := by
    field_simp
  have h5 : a / b + b / c + c / a ≤ (a / b) ^ 2 + (b / c) ^ 2 + (c / a) ^ 2 := by
    have h100 : (a / b) + (b / c) + (c / a) ≤ (a / b) ^ 2 + (b / c) ^ 2 + (c / a) ^ 2 := by
      have h33 : (a / b) * (b / c) * (c / a) = 1 := h4
      have ha1 : 0 < a / b := h1
      have hb1 : 0 < b / c := h2
      have hc1 : 0 < c / a := h3
      apply lemma_1 (a / b) (b / c) (c / a) (by positivity) (by positivity) (by positivity) h33
    linarith
  have h0 : a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 = (a / b) ^ 2 + (b / c) ^ 2 + (c / a) ^ 2 := by
    field_simp
  rw [h0] at *
  linarith