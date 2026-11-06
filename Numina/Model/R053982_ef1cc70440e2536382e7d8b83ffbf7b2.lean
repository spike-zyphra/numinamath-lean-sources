import Mathlib

theorem algebra_568 (a b g d : ℝ) (ha : a = 1 / 3) (hb : b = 1 / 4)
    (hg : g = 1 / 5) (hd : d = 1 / 6) (h : 0 < a ∧ 0 < b ∧ 0 < g ∧ 0 < d)
    (h1 : a * 1 + b * 1 + g * 1 + d * 1 = 1 / 6) :
    (6:ℝ) / (a + b + g + d) = 20 + 3 / 4 := by
  have h2 : a + b + g + d = 1 / 6 := by linarith
  have h3 : a + b + g + d = 19 / 20 := by
    rw [ha, hb, hg, hd]
    norm_num
  linarith