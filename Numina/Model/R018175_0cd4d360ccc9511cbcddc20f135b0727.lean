import Mathlib

theorem algebra_158278 {a b c m : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a * b * c > 0) (h2 : a + b + c > 1) (h3 : (2 * b + c - 1) / a = m)
    (h4 : (2 * c + a - 1) / b = m) (h5 : (2 * a + b - 1) / c = m) :
    m > 0 ∧ m - 3 < 0 := by
  have eq1 : 2 * b + c - 1 = a * m := by
    have : a ≠ 0 := ha
    field_simp at h3
    linarith
  have eq2 : 2 * c + a - 1 = b * m := by
    have : b ≠ 0 := hb
    field_simp at h4
    linarith
  have eq3 : 2 * a + b - 1 = c * m := by
    have : c ≠ 0 := hc
    field_simp at h5
    linarith

  constructor
  · -- Show that $m > 0$
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
              sq_pos_of_pos (show a * b * c > 0 by linarith), h1, h2, 
              mul_pos (show 0 < a + b + c - 1 by linarith) (show 0 < a + b + c - 1 by linarith)]
  · -- Show that $m - 3 < 0$
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
              sq_pos_of_pos (show a * b * c > 0 by linarith), h1, h2, 
              mul_pos (show 0 < a + b + c - 1 by linarith) (show 0 < a + b + c - 1 by linarith)]