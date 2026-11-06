import Mathlib

theorem inequalities_301956 (a b c : ℝ) (ha : abs a < 1) (hb : abs b < 1) (hc : abs c < 1) :
    (1 + a) * (1 + b) * (1 + c) > 0 ∧ (1 - a) * (1 - b) * (1 - c) > 0 := by
  have ha1 : -1 < a := by linarith [abs_lt.mp ha]
  have ha2 : a < 1 := by linarith [abs_lt.mp ha]
  have hb1 : -1 < b := by linarith [abs_lt.mp hb]
  have hb2 : b < 1 := by linarith [abs_lt.mp hb]
  have hc1 : -1 < c := by linarith [abs_lt.mp hc]
  have hc2 : c < 1 := by linarith [abs_lt.mp hc]
  have h1 : 1 + a > 0 := by linarith
  have h2 : 1 + b > 0 := by linarith
  have h3 : 1 + c > 0 := by linarith
  have h4 : (1 + a) * (1 + b) * (1 + c) > 0 := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h5 : 1 - a > 0 := by linarith
  have h6 : 1 - b > 0 := by linarith
  have h7 : 1 - c > 0 := by linarith
  have h8 : (1 - a) * (1 - b) * (1 - c) > 0 := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  constructor
  · exact h4
  · exact h8