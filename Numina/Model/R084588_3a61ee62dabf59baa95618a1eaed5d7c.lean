import Mathlib

theorem algebra_283716 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : b / c = 1 / a) (h2 : 0 / b = b / c) :
    (a + b - c) / (a - b + c) = 1 := by
  have h3 : (0 : ℝ) / b = 0 := by 
    simp [hb]
  have h4 : b / c = 0 := by 
    linarith [h2, h3]
  have h5 : b = 0 := by 
    have h6 : b / c = 0 := h4
    field_simp [hc] at h6 ⊢ 
    <;> linarith 
  contradiction