import Mathlib

theorem algebra_10286 : ⌈Real.sqrt 140⌉ = 12 := by
  have h1 : 11 < Real.sqrt 140 := by
    rw [Real.lt_sqrt] <;> norm_num
  have h2 : Real.sqrt 140 < (12 : ℝ) := by
    rw [Real.sqrt_lt] <;> norm_num
  simp [Int.ceil_eq_iff]
  constructor <;> (try norm_num) <;> try linarith [h1, h2]