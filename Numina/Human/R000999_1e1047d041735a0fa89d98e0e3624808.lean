import Mathlib

theorem algebra_19681 {a b c : ℕ} (ha : a^2 = 25) (hb : b^2 = 49)
    (hc : c * d = a * b) :
    c * d = 35 := by
  have ha' : a = 5 := by
    have : a ≤ 5 := by nlinarith
    interval_cases a <;> tauto
  have hb' : b = 7 := by
    have : b ≤ 7 := by nlinarith
    interval_cases b <;> tauto
  calc
    c * d = a * b := by rw [hc]
    _   = 5 * 7 := by rw [ha', hb']
    _   = 35    := by norm_num