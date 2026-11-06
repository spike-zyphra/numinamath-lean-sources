import Mathlib

theorem algebra_144976 {a b c d : ℝ} (ha : a + 3 = 3 * a) (hb : b + 4 = 4 * b) (hc : c + 5 = 5 * c) (hd : d + 6 = 6 * d) :
    a * b * c * d = 3 := by
  have ha' : a = 3 / 2 := by
    linarith
  have hb' : b = 4 / 3 := by
    linarith
  have hc' : c = 5 / 4 := by
    linarith
  have hd' : d = 6 / 5 := by
    linarith
  rw [ha', hb', hc', hd']
  norm_num