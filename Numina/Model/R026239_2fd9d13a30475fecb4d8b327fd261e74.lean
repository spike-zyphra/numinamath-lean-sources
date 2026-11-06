import Mathlib

theorem inequalities_3912
    (a b c : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 1)
    (hb : 0 ≤ b ∧ b ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1)
    (h : a + b + c = 2) :
    a^2 * b + b^2 * c + c^2 * a + a * b * c ≥ 1 := by
  have h1 : a ≥ 0 := by linarith
  have h2 : a ≤ 1 := by linarith
  have h3 : b ≥ 0 := by linarith
  have h4 : b ≤ 1 := by linarith
  have h5 : c ≥ 0 := by linarith
  have h6 : c ≤ 1 := by linarith
  have h7 : c = 2 - a - b := by linarith
  rw [h7]
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((2 - a - b) - 1),
          mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h3),
          mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr (show (2 - a - b) ≥ 0 by nlinarith)),
          mul_nonneg (sub_nonneg.mpr (show (2 - a - b) ≥ 0 by nlinarith)) (sub_nonneg.mpr h1),
          mul_nonneg (sub_nonneg.mpr (show (1 - a) ≥ 0 by nlinarith)) (sub_nonneg.mpr (show (1 - b) ≥ 0 by nlinarith)),
          mul_nonneg (sub_nonneg.mpr (show (1 - b) ≥ 0 by nlinarith)) (sub_nonneg.mpr (show (1 - (2 - a - b)) ≥ 0 by nlinarith)),
          mul_nonneg (sub_nonneg.mpr (show (1 - (2 - a - b)) ≥ 0 by nlinarith)) (sub_nonneg.mpr (show (1 - a) ≥ 0 by nlinarith))
          ]