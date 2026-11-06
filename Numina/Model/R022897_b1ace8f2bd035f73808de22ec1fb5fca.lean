import Mathlib

theorem algebra_12166 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h₁ : a + 2 * b = 1) (h₂ : c + 2 * d = 1) :
    1 / a + 1 / (b * c * d) ≥ 25 := by
  have ha1 : 0 < a := ha
  have hb1 : 0 < b := hb
  have hc1 : 0 < c := hc
  have hd1 : 0 < d := hd
  have h3 : b * c * d > 0 := by
    positivity
  have h4 : a * b * c * d > 0 := by
    positivity
  have h5 : 1 / a + 1 / (b * c * d) - 25 ≥ 0 := by
    have h6 : (b * c * d + a) ≥ 25 * (a * b * c * d) := by
      nlinarith [sq_nonneg (a - 1 / 5), sq_nonneg (b - 2 / 5), sq_nonneg (c - 1 / 2), sq_nonneg (d - 1 / 4),
        mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
        h₁, h₂, mul_pos (show 0 < a * b by positivity) (show 0 < c * d by positivity), 
        mul_pos (show 0 < a * c by positivity) (show 0 < b * d by positivity)]
    have h7 : (b * c * d + a) / (a * b * c * d) ≥ 25 := by
      have h8 : a * b * c * d > 0 := h4
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    have h8 : 1 / a + 1 / (b * c * d) - 25 = (b * c * d + a) / (a * b * c * d) - 25 := by
      field_simp [show 0 < a * b * c * d by positivity]
      all_goals ring
    linarith [h7, h8]
  linarith [h5]