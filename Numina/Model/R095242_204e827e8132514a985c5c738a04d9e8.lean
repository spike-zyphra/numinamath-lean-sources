import Mathlib

theorem algebra_237216 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a > b) (h1 : 2 * (a + b) = 3 * (a - b)) :
    a / b = 5 := by
  have h2 : 2 * a + 2 * b = 3 * a - 3 * b := by 
    linarith [h1]
  have h3 : a = 5 * b := by
    linarith
  have h4 : a / b = 5 := by 
    have hb' : b ≠ 0 := by linarith
    field_simp [hb']
    linarith [h3]
  exact h4