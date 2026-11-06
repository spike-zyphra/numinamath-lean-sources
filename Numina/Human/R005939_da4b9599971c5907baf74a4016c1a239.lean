import Mathlib

/-compute the unique real number y < 3 such that
√((3 - y) * (4 - y)) + √((4 - y) * (6 - y)) + √((6 - y) * (3 - y)) = y-/
theorem algebra_610826 {x: ℝ} (uniqueness: ∀ y: ℝ, y < 3 ∧
 √((3 - y) * (4 - y)) + √((4 - y) * (6 - y)) + √((6 - y) * (3 - y)) = y → y = x): x = 23 / 8 := by

 -- it suffices to show that 23/8 satisfies the equation --
  specialize uniqueness (23 / 8)
  have o: (23: ℝ) / 8 < 3 := by norm_num
  simp [o] at uniqueness
  symm
  apply uniqueness
  norm_num
  have id1: √9 = 3 := by
    rw [Real.sqrt_eq_iff_eq_sq]
    norm_num
    norm_num
    norm_num
  have id2 : √25 = 5 := by
    rw [Real.sqrt_eq_iff_eq_sq]
    norm_num
    norm_num
    norm_num
  have id3 :√64 = 8 := by
    rw [Real.sqrt_eq_iff_eq_sq]
    norm_num
    norm_num
    norm_num
  have id4: √225 = 15 := by
    rw [Real.sqrt_eq_iff_eq_sq]
    norm_num
    norm_num
    norm_num
  simp [id1, id2, id3, id4]
  norm_num