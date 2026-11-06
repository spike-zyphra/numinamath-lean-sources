import Mathlib

theorem inequalities_598839
    (a b c : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 1)
    (hb : 0 ≤ b ∧ b ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1) :
    a^2 + b^2 + c^2 ≤ a^2 * b + b^2 * c + c^2 * a + 1 := by
  have h1 : 0 ≤ a := ha.1
  have h2 : a ≤ 1 := ha.2
  have h3 : 0 ≤ b := hb.1
  have h4 : b ≤ 1 := hb.2
  have h5 : 0 ≤ c := hc.1
  have h6 : c ≤ 1 := hc.2
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h3),
            mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr h5),
            mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h5),
            mul_nonneg (sub_nonneg.mpr (show (1 : ℝ) - a ≥ 0 by linarith)) (sub_nonneg.mpr (show (1 : ℝ) - b ≥ 0 by linarith)),
            mul_nonneg (sub_nonneg.mpr (show (1 : ℝ) - b ≥ 0 by linarith)) (sub_nonneg.mpr (show (1 : ℝ) - c ≥ 0 by linarith)),
            mul_nonneg (sub_nonneg.mpr (show (1 : ℝ) - c ≥ 0 by linarith)) (sub_nonneg.mpr (show (1 : ℝ) - a ≥ 0 by linarith)),
            mul_nonneg h1 (sub_nonneg.mpr h3),
            mul_nonneg h3 (sub_nonneg.mpr h5),
            mul_nonneg h5 (sub_nonneg.mpr h1),
            mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h4),
            mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr h6),
            mul_nonneg (sub_nonneg.mpr h5) (sub_nonneg.mpr h2)
          ]