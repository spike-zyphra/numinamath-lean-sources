import Mathlib
open Real

theorem algebra_96840 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
(h1 : b-a=9-b) (h2 : b/a=a/3) : a + b = 11 + 1 / 4 := by
  have h3 : a ≠ 0 := by linarith
  have h4 : 3 * b = a ^ 2 := by
    field_simp [h3] at h2
    nlinarith
  -- Simplify h1 to 2 * b - a = 9
  have h5 : 2 * b - a = 9 := by 
    linarith
  have h6 : a = 2 * b - 9 := by
    linarith
  rw [h6] at h4
  have h7 : 4 * b ^ 2 - 39 * b + 81 = 0 := by
    nlinarith
  have h8 : (b - 27 / 4) * (b - 3) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- Case where b = 27/4
    have hb2 : b = 27 / 4 := by linarith
    have ha2 : a = 9 / 2 := by
      linarith
    linarith
  · -- Case where b = 3
    have hb3 : b = 3 := by linarith
    have ha3 : a = -3 := by
      nlinarith
    linarith