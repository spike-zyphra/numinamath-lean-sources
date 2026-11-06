import Mathlib

theorem inequalities_106217 {a b : ℝ} (ha : 0 < b) (hb : b < a) :
    4 * a^3 * (a - b) ≥ a^4 - b^4 := by
  suffices 0 ≤ 3 * a^4 - 4 * a^3 * b + b^4 by
    nlinarith
  have h : 3 * a^4 - 4 * a^3 * b + b^4 = (a - b) ^ 2 * (3 * a^2 + 2 * a * b + b^2) := by
    ring_nf
  rw [h]
  have h1 : (a - b) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h2 : 3 * a^2 + 2 * a * b + b^2 > 0 := by
    nlinarith [sq_nonneg (a - b), sq_pos_of_pos (show 0 < b by linarith)]
  have h3 : (a - b) ^ 2 * (3 * a^2 + 2 * a * b + b^2) ≥ 0 := by
    apply mul_nonneg
    · exact h1
    · linarith
  linarith