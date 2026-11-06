import Mathlib

theorem algebra_315186 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 1 / a + 1 / b = 1 / (2 + 2 / 5)) (h2 : 1 / b + 1 / c = 1 / (3 + 3 / 4))
    (h3 : 1 / a + 1 / c = 1 / (2 + 6 / 7)) (h4 : 180000 / a + 150000 / b + 160000 / c = 177000) :
    min (min (180000 / a) (150000 / b)) (160000 / c) = 177000 := by
  field_simp at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  have h5 : min (min (180000 / a) (150000 / b)) (160000 / c) = 177000 := by
    nlinarith [show 180000 / a - 177000 ≥ 0 by nlinarith, 
      show 150000 / b - 177000 ≥ 0 by nlinarith, 
      show 160000 / c - 177000 ≥ 0 by nlinarith]
  linarith