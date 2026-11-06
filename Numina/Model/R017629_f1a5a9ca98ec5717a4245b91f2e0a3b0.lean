import Mathlib

theorem algebra_305832 (a b c x y z k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h1 : a + 2 * x = k) (h2 : 2 * b + 3 * y = k)
    (h3 : 3 * c + 4 * z = k) :
    0 < (a * x + b * y + c * z) ∧ (a * x + b * y + c * z) ≤ 3 / 16 * k ^ 2 := by

  have h4 : 0 < a * x + b * y + c * z := by
    have hx_pos : 0 < x := hx
    have ha_pos : 0 < a := ha
    have hb_pos : 0 < b := hb
    have hy_pos : 0 < y := hy
    have hc_pos : 0 < c := hc
    have hz_pos : 0 < z := hz
    positivity

  have h5 : a * x + b * y + c * z ≤ 3 / 16 * k ^ 2 := by
    nlinarith [sq_nonneg (a - k / 2), sq_nonneg (x - k / 4), sq_nonneg (b - k / 4),
          sq_nonneg (y - k / 6), sq_nonneg (c - k / 6), sq_nonneg (z - k / 8),
          h1, h2, h3,
          mul_pos ha hx, mul_pos hb hy, mul_pos hc hz,
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
         ]

  constructor
  · exact h4
  · exact h5