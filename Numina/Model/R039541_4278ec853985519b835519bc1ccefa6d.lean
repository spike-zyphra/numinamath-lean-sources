import Mathlib

theorem algebra_212726 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a + 20 * b = c + 20 * d) (h2 : c + 20 * d = 2) :
    1 / a + 1 / (b * c * d) ≥ 441 / 2 := by

  have ha2 : a = 2 - 20 * b := by 
    nlinarith
  have hc2 : c = 2 - 20 * d := by 
    nlinarith
  have hb10 : b < 1 / 10 := by 
    nlinarith [show a > 0 by linarith, ha2]
  have hd10 : d < 1 / 10 := by 
    nlinarith [show c > 0 by linarith, hc2]
  have h9 : 1 / a + 1 / (b * c * d) - 441 / 2 ≥ 0 := by
    rw [show a = 2 - 20 * b by linarith, show c = 2 - 20 * d by linarith]
    have h10 : 0 < b := hb
    have h11 : 0 < d := hd
    have h12 : 0 < (2 - 20 * b : ℝ) := by
      nlinarith
    have h13 : 0 < (2 - 20 * d : ℝ) := by
      nlinarith
    have h14 : (1 / (2 - 20 * b) + 1 / (b * (2 - 20 * d) * d) - 441 / 2) ≥ 0 := by 
      have h15 : 0 < (2 - 20 * b : ℝ) := h12
      have h16 : 0 < b := h10
      have h17 : 0 < (2 - 20 * d : ℝ) := h13
      have h18 : 0 < d := h11
      have h19 : 0 < b * (2 - 20 * d) * d := by positivity
      have h20 : (1 / (2 - 20 * b) + 1 / (b * (2 - 20 * d) * d) - 441 / 2) =
          (2 * b * (2 - 20 * d) * d + (2 - 20 * b) * 2 - 441 * (2 - 20 * b) * b * (2 - 20 * d) * d) / (2 * (2 - 20 * b) * b * (2 - 20 * d) * d) := by
        field_simp
        ring
      rw [h20] at *
      apply div_nonneg
      nlinarith [sq_nonneg (b - 2 / 21), sq_nonneg (d - 1 / 20), sq_nonneg (b * (b - 2 / 21)), sq_nonneg (d * (d - 1 / 20)), 
          sq_nonneg ((2 - 20 * b) - (2 / 21)), sq_nonneg ((2 - 20 * d) - 1), 
          mul_pos h10 h11, mul_pos h10 h12, 
          mul_pos h12 h11, 
          mul_pos (show 0 < (2 - 20 * b : ℝ) by nlinarith) (show 0 < (2 - 20 * d : ℝ) by nlinarith)
          ]
      all_goals positivity
    linarith
  linarith