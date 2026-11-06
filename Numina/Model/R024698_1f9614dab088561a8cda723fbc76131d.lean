import Mathlib

theorem algebra_198543 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 1 / a = 6) (h2 : 1 / b = 8) (h3 : 1 / c = 10) (h4 : 1 / (a + b + c) = 12 - 8) :
    1 / a = 8.6 := by
  have ha' : a = 1 / 6 := by
    have hne : a ≠ 0 := by linarith
    field_simp at h1 ⊢
    linarith
  have hb' : b = 1 / 8 := by
    have hne : b ≠ 0 := by linarith
    field_simp at h2 ⊢
    linarith
  have hc' : c = 1 / 10 := by
    have hne : c ≠ 0 := by linarith
    field_simp at h3 ⊢
    linarith
  have h5 : a + b + c = 47 / 120 := by
    rw [ha', hb', hc']
    norm_num
  have h7 : 1 / (a + b + c) = 4 := by
    linarith
  rw [show a + b + c = 47 / 120 by linarith [h5]] at h7
  norm_num at h7 ⊢
  all_goals linarith