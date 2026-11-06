import Mathlib

theorem algebra_170086 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 2.4) (h1 : a = 1.5) (h2 : b = 0.9) (h3 : c * 2 = 240) :
    a * 240 / 3 = 210 ∧ b * 240 / 3 = 30 := by
  have h4 : c = 0 := by
    rw [h1, h2] at h
    norm_num at h ⊢
    linarith
  have h5 : c > 0 := by linarith
  have h6 : c = 120 := by 
    linarith 
  nlinarith [h4, h5, h6]