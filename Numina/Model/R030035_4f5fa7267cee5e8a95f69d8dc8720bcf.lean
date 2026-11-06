import Mathlib

theorem algebra_21852 : ⌈-Real.sqrt 23⌉ = -4 := by
  have h1 : 4 < Real.sqrt 23 := by 
    rw [Real.lt_sqrt] <;> norm_num
  have h2 : Real.sqrt 23 < 5 := by 
    rw [Real.sqrt_lt] <;> norm_num
  have h3 : -5 < -Real.sqrt 23 := by 
    linarith [h2]
  have h4 : -Real.sqrt 23 ≤ -4 := by 
    linarith [h1]
  rw [Int.ceil_eq_iff]
  constructor <;> (try norm_num) <;> linarith