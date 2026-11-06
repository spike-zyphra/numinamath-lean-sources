import Mathlib

theorem inequalities_90605 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    9 * a * b * c ≤ a * b + a * c + b * c ∧
    a * b + a * c + b * c < 1 / 4 + 3 * a * b * c := by
  constructor
  · -- Prove that $9abc \leq ab + ac + bc$.
    have h1 : c = 1 - a - b := by linarith
    rw [h1] at *
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)),
      mul_pos ha hb, mul_pos ha (show 0 < 1 - a - b by nlinarith), mul_pos hb (show 0 < 1 - a - b by nlinarith)]
  · -- Prove that $ab + ac + bc < \frac{1}{4} + 3abc$.
    have h1 : c = 1 - a - b := by linarith
    rw [h1] at *
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)),
      sq_nonneg (a + b - 1 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2),
      mul_pos ha hb, mul_pos ha (show 0 < 1 - a - b by nlinarith), mul_pos hb (show 0 < 1 - a - b by nlinarith)]