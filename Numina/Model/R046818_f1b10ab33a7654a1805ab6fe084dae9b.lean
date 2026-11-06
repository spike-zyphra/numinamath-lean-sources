import Mathlib

open Real Set

theorem algebra_113478 :
  IsGreatest {t : ℝ | ∃ x y z : ℝ, x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ z ∈ Icc 0 1 ∧ t = x^2 * y + y^2 * z + z^2 * x - x^2 * z - y^2 * x - z^2 * y} (1/4) := by
  constructor
  · -- Show that 1/4 is achievable with (1, 1/2, 0)
    use 1, 1 / 2, (0 : ℝ)
    norm_num [mem_Icc]
    <;> norm_num [mem_Icc]
  · -- Show that 1/4 is the greatest
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, ht⟩
    rcases hx with ⟨hx0, hx1⟩
    rcases hy with ⟨hy0, hy1⟩
    rcases hz with ⟨hz0, hz1⟩
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (z - 1 / 2),
      sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (z - 1 / 2),
      mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr hy0),
      mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr hz0),
      mul_nonneg (sub_nonneg.mpr hy0) (sub_nonneg.mpr hz0),
      mul_nonneg (sub_nonneg.mpr (show 0 ≤ 1 - x by linarith)) (sub_nonneg.mpr (show 0 ≤ 1 - y by linarith)),
      mul_nonneg (sub_nonneg.mpr (show 0 ≤ 1 - y by linarith)) (sub_nonneg.mpr (show 0 ≤ 1 - z by linarith)),
      mul_nonneg (sub_nonneg.mpr (show 0 ≤ 1 - z by linarith)) (sub_nonneg.mpr (show 0 ≤ 1 - x by linarith)),
      mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr (show 0 ≤ 1 - y by linarith)),
      mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr (show 0 ≤ 1 - z by linarith)),
      mul_nonneg (sub_nonneg.mpr hy0) (sub_nonneg.mpr (show 0 ≤ 1 - x by linarith)),
      mul_nonneg (sub_nonneg.mpr hy0) (sub_nonneg.mpr (show 0 ≤ 1 - z by linarith)),
      mul_nonneg (sub_nonneg.mpr hz0) (sub_nonneg.mpr (show 0 ≤ 1 - x by linarith)),
      mul_nonneg (sub_nonneg.mpr hz0) (sub_nonneg.mpr (show 0 ≤ 1 - y by linarith))
      ]