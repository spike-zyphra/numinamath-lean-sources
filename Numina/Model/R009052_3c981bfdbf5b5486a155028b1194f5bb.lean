import Mathlib

theorem algebra_10945 (d area perimeter: ℝ) (hd : d = 8) (harea : area = √3 * d * d / 4)
    (hperimeter : perimeter = 3 * d) : area / perimeter = 2 * √3 / 3 := by
  rw [harea, hperimeter, hd]
  have h1 : (√3 * (8 : ℝ) * (8 : ℝ) / 4) = 16 * √3 := by
    ring_nf
  have h2 : (3 * (8 : ℝ)) = (24 : ℝ) := by
    norm_num
  rw [h1, h2]
  field_simp
  <;> ring_nf <;> field_simp <;> linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num : (0:ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]