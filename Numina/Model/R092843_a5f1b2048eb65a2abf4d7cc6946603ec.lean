import Mathlib

theorem other_260202 (a b c d : ℝ)
    (ha : 0 < a ∧ a = 1 / 3) (hb : 0 < b ∧ b = 1 / 4)
    (hc : 0 < c ∧ c = 1 / 5) (hd : 0 < d ∧ d = 1 / 6)
    (h : 1 / 6 * a + 1 / 4 * b + 1 / 5 * c + 1 / 6 * d = 1) :
    1 / (a + b + c + d) = 20 + 3 / 4 := by 
  have ha1 : a = 1 / 3 := by linarith
  have hb1 : b = 1 / 4 := by linarith
  have hc1 : c = 1 / 5 := by linarith
  have hd1 : d = 1 / 6 := by linarith
  rw [ha1, hb1, hc1, hd1] at h
  norm_num at h
  all_goals linarith -- Since the hypothesis is inconsistent, any goal is true