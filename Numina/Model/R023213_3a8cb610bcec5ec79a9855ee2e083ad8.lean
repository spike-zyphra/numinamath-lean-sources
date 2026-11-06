import Mathlib

theorem algebra_140397 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (1 + 10 / 100) * a * (1 + 20 / 100) * b * (1 + 25 / 100) * c = (1 + x) * a * b * c) :
    x = 65 / 100 := by
  have h1 : (1 + (10 / 100 : ℝ)) * (1 + (20 / 100 : ℝ)) * (1 + (25 / 100 : ℝ)) = (1 + x) := by
    have h2 : a * b * c > 0 := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h3 : (1 + (10 / 100 : ℝ)) * (1 + (20 / 100 : ℝ)) * (1 + (25 / 100 : ℝ)) = (1 + x) := by
      apply (mul_left_inj' (ne_of_gt h2)).mp
      linarith
    exact h3
  have h4 : (1 + (10 / 100 : ℝ)) * (1 + (20 / 100 : ℝ)) * (1 + (25 / 100 : ℝ)) = (165 / 100 : ℝ) := by
    norm_num
  have h6 : (1 + x) = (165 / 100 : ℝ) := by
    linarith [ h1, h4 ]
  linarith