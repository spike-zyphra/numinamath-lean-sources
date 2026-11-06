import Mathlib

theorem algebra_11847 : ⌈√2⌉ + ⌈√22⌉ + ⌈√222⌉ = 22 := by

  have h1 : ⌈√2⌉ = 2 := by
    have h1 : 1 < √2 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h2 : √2 < 2 := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.ceil_eq_iff]
    constructor <;> (try norm_num) <;> linarith [h1, h2]

  have h2 : ⌈√22⌉ = 5 := by
    have h1 : 4 < √22 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h2 : √22 < 5 := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.ceil_eq_iff]
    constructor <;> (try norm_num) <;> linarith [h1, h2]

  have h3 : ⌈√222⌉ = 15 := by
    have h1 : 14 < √222 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h2 : √222 < 15 := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.ceil_eq_iff]
    constructor <;> (try norm_num) <;> linarith [h1, h2]

  rw [h1, h2, h3]
  all_goals norm_num