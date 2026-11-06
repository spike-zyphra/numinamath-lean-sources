import Mathlib

theorem algebra_10912 : ⌊Real.sqrt 63⌋ = 7 := by
  have h1 : 7 < Real.sqrt 63 := by
    rw [Real.lt_sqrt] <;> norm_num
  have h2 : Real.sqrt 63 < 8 := by
    rw [Real.sqrt_lt] <;> norm_num
  have h3 : ⌊Real.sqrt 63⌋ = 7 := by
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  exact h3