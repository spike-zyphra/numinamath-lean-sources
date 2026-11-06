import Mathlib

theorem algebra_170267 {a d : ℝ} (ha : a ≠ 0) (h : a^2 - 6 * a * d + 8 * d^2 = 0) :
    d / a = 1 / 2 ∨ d / a = 1 / 4 := by
  have h1 : (a - 2 * d) * (a - 4 * d) = 0 := by 
    linarith [h]
  cases' (mul_eq_zero.mp h1) with h2 h3
  · -- Case where $a - 2d = 0$
    have ha2 : a = 2 * d := by linarith
    have hda1 : d / a = 1 / 2 := by
      field_simp [ha]
      linarith
    left
    exact hda1
  · -- Case where $a - 4d = 0$
    have ha4 : a = 4 * d := by linarith
    have hda2 : d / a = 1 / 4 := by
      field_simp [ha]
      linarith
    right
    exact hda2