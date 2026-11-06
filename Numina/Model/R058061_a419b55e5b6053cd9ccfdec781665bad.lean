import Mathlib

theorem algebra_97998 (a b : ℝ) (ha : 5 * a + b > 51.00) (hb : 3 * a - b = 21.00) :
    a > 9 ∧ b > 6 := by
  have h1 : a > 9 := by
    have h2 : b = 3 * a - 21.00 := by
      linarith [hb]
    rw [h2] at ha
    norm_num at ha ⊢
    linarith
  have h3 : b > 6 := by
    have h2 : b = 3 * a - 21.00 := by
      linarith [hb]
    rw [h2]
    linarith [h1]
  constructor
  · exact h1
  · exact h3