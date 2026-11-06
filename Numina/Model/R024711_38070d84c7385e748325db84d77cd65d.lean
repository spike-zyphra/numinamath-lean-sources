import Mathlib

theorem algebra_285456 : ⌊Real.sqrt (2007^2 - 20070 + 31)⌋ = 2002 := by
  have h1 : Real.sqrt (2007^2 - 20070 + 31) = Real.sqrt (4008010 : ℝ) := by
    norm_num
  rw [h1]
  have h2 : 2002 < Real.sqrt (4008010 : ℝ) := by
    rw [Real.lt_sqrt] <;> norm_num
  have h3 : Real.sqrt (4008010 : ℝ) < 2003 := by
    rw [Real.sqrt_lt] <;> norm_num
  have h4 : ⌊Real.sqrt (4008010 : ℝ)⌋ = 2002 := by
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith [h2, h3]
  exact h4