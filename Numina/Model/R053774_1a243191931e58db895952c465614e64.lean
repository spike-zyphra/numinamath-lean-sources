import Mathlib

theorem algebra_21531 : ⌈Real.sqrt 20⌉^2 = 25 := by
  have h1 : 4 < Real.sqrt 20 := by
    rw [Real.lt_sqrt] <;> norm_num
  have h2 : Real.sqrt 20 ≤ 5 := by
    have h3 : Real.sqrt 20 ≤ Real.sqrt 25 := Real.sqrt_le_sqrt (by norm_num)
    have h4 : Real.sqrt 25 = (5 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    linarith [h3, h4]
  have h5 : ⌈Real.sqrt 20⌉ = 5 := by
    rw [Int.ceil_eq_iff]
    constructor <;> (try norm_num) <;> linarith [h1, h2]
  rw [h5]
  all_goals norm_num