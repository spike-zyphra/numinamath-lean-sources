import Mathlib

theorem inequalities_73208 (a b c d : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hc : 0 < c ∧ c < 1) (hd : 0 < d ∧ d < 1) (h : a * b * c * d = (1 - a) * (1 - b) * (1 - c) * (1 - d)) :
    (a + b + c + d) - (a + c) * (b + d) ≥ 1 := by
  have ha1 : 0 < a := ha.1
  have ha2 : a < 1 := ha.2
  have hb1 : 0 < b := hb.1
  have hb2 : b < 1 := hb.2
  have hc1 : 0 < c := hc.1
  have hc2 : c < 1 := hc.2
  have hd1 : 0 < d := hd.1
  have hd2 : d < 1 := hd.2
  nlinarith [sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a + c - 1), sq_nonneg (b + d - 1),
    mul_pos (show 0 < a by linarith) (show 0 < 1 - a by linarith), 
    mul_pos (show 0 < b by linarith) (show 0 < 1 - b by linarith), 
    mul_pos (show 0 < c by linarith) (show 0 < 1 - c by linarith), 
    mul_pos (show 0 < d by linarith) (show 0 < 1 - d by linarith)]