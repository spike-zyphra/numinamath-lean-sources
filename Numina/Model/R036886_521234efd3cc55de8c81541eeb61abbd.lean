import Mathlib

theorem inequalities_64413 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / (a + 2019) + 1 / (b + 2019) + 1 / (c + 2019) = 1 / 2019) :
    a * b * c ≥ 4038 ^ 3 := by
  have ha' : 0 < a + 2019 := by linarith 
  have hb' : 0 < b + 2019 := by linarith 
  have hc' : 0 < c + 2019 := by linarith 
  have ha_pos : a + 2019 ≠ 0 := by linarith
  have hb_pos : b + 2019 ≠ 0 := by linarith
  have hc_pos : c + 2019 ≠ 0 := by linarith
  field_simp [ha_pos, hb_pos, hc_pos] at h ⊢
  nlinarith [sq_nonneg (a * b * c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c)]