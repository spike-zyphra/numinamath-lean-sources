import Mathlib

theorem algebra_20844 : IsGreatest {k : ℝ | ∃ x y : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 ∧ k = x^2*y - x*y^2 } (1/4) := by
  constructor
  · -- Show 1/4 is in the set
    use 1, 1 / 2
    norm_num
  · -- Show 1/4 is greatest in the set
    intro k hk
    rcases hk with ⟨x, y, hx1, hx2, hy1, hy2, hk⟩
    have h1 : x ^ 2 * y - x * y ^ 2 ≤ 1 / 4 := by
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (x - y), mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hx2), mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hy2), mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1), mul_nonneg (sub_nonneg.mpr (show (0 : ℝ) ≤ 1 - x by linarith)) (sub_nonneg.mpr (show (0 : ℝ) ≤ 1 - y by linarith)), mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (show (0 : ℝ) ≤ 1 - x by linarith)), mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr (show (0 : ℝ) ≤ 1 - y by linarith)), sq_nonneg (x * y - 1 / 4), sq_nonneg ((x - y) - 0)]
    linarith [h1, hk]