import Mathlib

theorem algebra_102095 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 1 / a = 5) (h2 : 1 / b = 7) (h3 : 1 / c = 3) :
    1 / (a + b - c) = 105 := by
  have ha' : a = 1 / 5 := by 
    field_simp [show a ≠ 0 by linarith] at h1 ⊢
    linarith
  have hb' : b = 1 / 7 := by 
    field_simp [show b ≠ 0 by linarith] at h2 ⊢
    linarith
  have hc' : c = 1 / 3 := by 
    field_simp [show c ≠ 0 by linarith] at h3 ⊢
    linarith
  have h4 : a + b - c = 1 / 105 := by 
    rw [ha', hb', hc']
    norm_num
  rw [h4]
  field_simp
  all_goals linarith