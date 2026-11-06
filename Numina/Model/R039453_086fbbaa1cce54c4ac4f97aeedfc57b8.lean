import Mathlib.Data.Real.Basic
import Mathlib.Analysis.MeanInequalities

open Real Set
open scoped BigOperators

theorem algebra_21183 :
  IsGreatest {t : ℝ | ∃ x y z : ℝ, x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ z ∈ Icc 0 1 ∧
    t = x^2 * y + y^2 * z + z^2 * x - x * y^2 - y * z^2 - z * x^2} (1/4) := by
  constructor
  · -- Show that 1/4 is in the set
    use 1, 1 / 2, (0 : ℝ)
    norm_num [mem_Icc]
    <;> norm_num 
  · -- Show that 1/4 is greatest in the set
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, ht⟩
    rcases hx with ⟨hx0, hx1⟩
    rcases hy with ⟨hy0, hy1⟩
    rcases hz with ⟨hz0, hz1⟩
    have h1 : x^2 * y + y^2 * z + z^2 * x - x * y^2 - y * z^2 - z * x^2 ≤ 1/4 := by 
      nlinarith [sq_nonneg (x - 1/2), sq_nonneg (y - 1/2), sq_nonneg (z - 1/2), mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr hy0), 
        mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr hz0), 
        mul_nonneg (sub_nonneg.mpr hy0) (sub_nonneg.mpr hz0), 
        mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr (show (1 : ℝ) - x ≥ 0 by linarith)), 
        mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr (show (1 : ℝ) - y ≥ 0 by linarith)), 
        mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr (show (1 : ℝ) - z ≥ 0 by linarith)), 
        mul_nonneg (sub_nonneg.mpr hy0) (sub_nonneg.mpr (show (1 : ℝ) - x ≥ 0 by linarith)), 
        mul_nonneg (sub_nonneg.mpr hy0) (sub_nonneg.mpr (show (1 : ℝ) - z ≥ 0 by linarith)), 
        mul_nonneg (sub_nonneg.mpr hz0) (sub_nonneg.mpr (show (1 : ℝ) - x ≥ 0 by linarith)), 
        mul_nonneg (sub_nonneg.mpr hz0) (sub_nonneg.mpr (show (1 : ℝ) - y ≥ 0 by linarith)), 
        mul_nonneg (sub_nonneg.mpr (show (1 : ℝ) - x ≥ 0 by linarith)) (sub_nonneg.mpr (show (1 : ℝ) - y ≥ 0 by linarith)), 
        mul_nonneg (sub_nonneg.mpr (show (1 : ℝ) - x ≥ 0 by linarith)) (sub_nonneg.mpr (show (1 : ℝ) - z ≥ 0 by linarith)), 
        mul_nonneg (sub_nonneg.mpr (show (1 : ℝ) - y ≥ 0 by linarith)) (sub_nonneg.mpr (show (1 : ℝ) - z ≥ 0 by linarith))
      ]
    linarith