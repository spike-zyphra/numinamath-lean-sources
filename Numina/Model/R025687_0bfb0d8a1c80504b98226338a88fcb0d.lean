import Mathlib

theorem algebra_176762 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : 15 * a + 10 * b = 1) (h2 : 15 * (1 / 6) + 10 * (1 / 4) = 1 + 7 * (a + b)) :
    1 / a = 20 ∧ 1 / b = 20 := by
  norm_num at h2 
  have h3 : a + b = 4 / 7 := by 
    linarith
  have h4 : b = 4 / 7 - a := by
    linarith [h3]
  rw [h4] at h1 
  have h5 : 15 * a + 10 * (4 / 7 - a) = 1 := by 
    linarith
  have h6 : a < 0 := by 
    linarith
  linarith