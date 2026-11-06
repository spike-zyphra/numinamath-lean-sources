import Mathlib

theorem algebra_20435 : ⌊|(-23/9 : ℝ)|⌋ = 2 := by
  have h1 : |(-23 / 9 : ℝ)| = (23 / 9 : ℝ) := by
    norm_num [abs_of_neg]
  rw [h1]
  norm_num [Int.floor_eq_iff]