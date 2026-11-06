import Mathlib

theorem algebra_1258 {a b : ℝ} (h : a + b = 0) (h' : |a - 2 * b| = 3 / 2) :
    (2 * a - a * b - b ^ 2 + 2) / (a ^ 2 + a * b + b - 1) = -2 := by
  have h1 : b = -a := by linarith
  rw [h1] at h'
  cases eq_or_eq_neg_of_abs_eq h' with
  | inl h2 =>
    have ha : a = 1 / 2 := by linarith
    have hb : b = -1 / 2 := by linarith [h1, ha]
    rw [ha, hb]
    norm_num
  | inr h2 =>
    have ha : a = -1 / 2 := by linarith
    have hb : b = 1 / 2 := by linarith [h1, ha]
    rw [ha, hb]
    norm_num