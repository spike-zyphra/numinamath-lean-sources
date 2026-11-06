import Mathlib

theorem inequalities_140192 (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : 0 < x ∧ x < a) :
    (a - x) ^ 6 - 3 * a * (a - x) ^ 5 + 5 / 2 * a ^ 2 * (a - x) ^ 4 -
    1 / 2 * a ^ 4 * (a - x) ^ 2 < 0 := by
  have h1 : 0 < x := hx.1
  have h2 : x < a := hx.2
  have h3 : (a - x) ^ 6 - 3 * a * (a - x) ^ 5 + 5 / 2 * a ^ 2 * (a - x) ^ 4 -
    1 / 2 * a ^ 4 * (a - x) ^ 2 =
    (x ^ 2 * (a - x) ^ 2) * ((a - x) ^ 2 - a * (a - x) - 1 / 2 * a ^ 2) := by
      ring
  rw [h3]
  have h4 : x ^ 2 * (a - x) ^ 2 > 0 := by
    have hx2 : x ^ 2 > 0 := by
      nlinarith
    have ha2x : (a - x) ^ 2 > 0 := by
      nlinarith
    nlinarith
  have h5 : (a - x) ^ 2 - a * (a - x) - 1 / 2 * a ^ 2 < 0 := by
    nlinarith [sq_nonneg ((a - x) - a * (1 + Real.sqrt 3) / 2), sq_nonneg ((a - x) - a * (1 - Real.sqrt 3) / 2), Real.sqrt_pos.mpr ha, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  apply mul_neg_of_pos_of_neg
  · linarith
  · linarith