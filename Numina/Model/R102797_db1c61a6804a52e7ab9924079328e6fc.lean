import Mathlib

theorem algebra_10678 {a b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0) (h1 : a / b = 2) (h2 : b / c = 3 / 4) :
    c / a = 2 / 3 := by
  have h3 : a = 2 * b := by 
    field_simp [hb] at h1 ⊢
    linarith
  have h4 : b = (3 / 4) * c := by
    field_simp [hc] at h2 ⊢
    linarith
  have h5 : c = (4 / 3) * b := by 
    linarith [h4]
  have ha : a ≠ 0 := by 
    by_contra h
    rw [h] at h3
    have : b = 0 := by linarith 
    contradiction
  rw [show c = (4 / 3) * b by linarith [h5], show a = 2 * b by linarith [h3]]
  field_simp [show b ≠ 0 by exact hb]
  <;> 
  linarith
  <;> 
  try { contradiction }