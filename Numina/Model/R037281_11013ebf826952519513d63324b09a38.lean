import Mathlib

theorem inequalities_262199 (a b c : ℝ) 
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 3) 
    (hmax : a ≤ 2) (hmax' : b ≤ 2) (hmax'' : c ≤ 2) :
    a^2 + b^2 + c^2 + 3 * a * b * c < 9 := by
  have h1 : c = 3 - a - b := by linarith 
  rw [h1] 
  nlinarith [mul_pos ha hb, mul_pos hb (show (0 : ℝ) < 3 - a - b by nlinarith), mul_pos ha (show (0 : ℝ) < 3 - a - b by nlinarith), 
           mul_nonneg (sub_nonneg.mpr hmax) (sub_nonneg.mpr hmax'), 
           mul_nonneg (sub_nonneg.mpr hmax) (sub_nonneg.mpr (show 3 - a - b ≤ 2 by nlinarith)), 
           mul_nonneg (sub_nonneg.mpr hmax') (sub_nonneg.mpr (show 3 - a - b ≤ 2 by nlinarith)), 
           mul_pos (show (0 : ℝ) < 3 - a - b by nlinarith) (show (0 : ℝ) < 3 - a - b by nlinarith)]