import Mathlib

theorem algebra_115700 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a * 2 + b * 2 = 1) (h2 : a / 3 + b * 3 = 1) :
    b / a = 5 / 3 := by
  have h4 : a = 3 / 16 := by
    linarith [h1, h2]
  have h5 : b = 5 / 16 := by
    linarith [h1, h4]
  have h6 : b / a = 5 / 3 := by
    rw [h5, h4]
    field_simp
    all_goals
      linarith
  exact h6