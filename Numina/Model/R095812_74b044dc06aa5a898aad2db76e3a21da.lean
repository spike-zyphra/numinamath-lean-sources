import Mathlib

theorem algebra_2405 {a b : ℝ} (ha : a < 0) (hb : b > 0) (habs : |a| < |b|) :
    (a - b) * (a * b + a) > 0 := by
  have h1 : a < 0 := ha
  have h2 : b > 0 := hb
  have h3 : |a| = -a := by
    rw [abs_of_neg ha]
  have h4 : |b| = b := by
    rw [abs_of_pos hb]
  rw [h3, h4] at habs
  have h5 : a > -b := by linarith
  have h6 : a - b < 0 := by linarith
  have h7 : a * (b + 1) < 0 := by
    apply mul_neg_of_neg_of_pos
    linarith
    linarith
  have h8 : a * b + a = a * (b + 1) := by ring
  have h9 : a * b + a < 0 := by
    linarith [h7, h8]
  apply mul_pos_of_neg_of_neg
  all_goals linarith