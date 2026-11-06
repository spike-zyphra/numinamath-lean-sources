import Mathlib

open Real
open scoped BigOperators

theorem algebra_597864 :
  IsLeast {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y * z * (x + y + z) = 1 ∧ t = (x + y) * (x + z)} 2 := by 
  constructor
  · -- First part: show 2 is in the set
    use Real.sqrt 2 - 1, 1, 1
    constructor
    · -- Show sqrt 2 - 1 > 0
      have h1 : Real.sqrt 2 > 1 := by
        have h2 : Real.sqrt 2 > Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        have h3 : Real.sqrt 1 = 1 := Real.sqrt_one
        linarith [h2, h3]
      linarith [h1]
    constructor
    · -- Show 1 > 0
      norm_num
    constructor
    · -- Show 1 > 0
      norm_num
    constructor
    · -- Show (sqrt 2 - 1) * 1 * 1 * (sqrt 2 - 1 + 1 + 1) = 1
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [h1, Real.sqrt_nonneg 2]
    · -- Show 2 = (sqrt 2 - 1 + 1) * (sqrt 2 - 1 + 1)
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [h1, Real.sqrt_nonneg 2]
  · -- Show 2 is the least element in the set
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, heq⟩
    have h2 : (x + y) * (x + z) ≥ 2 := by
      have h3 : x * (x + y + z) + y * z ≥ 2 := by
        have h4 : x * (x + y + z) * (y * z) = 1 := by
          nlinarith 
        have h5 : x * (x + y + z) > 0 := by
          apply mul_pos 
          linarith 
          linarith 
        have h6 : y * z > 0 := by 
          apply mul_pos 
          linarith 
          linarith 
        have h7 : x * (x + y + z) + y * z - 2 ≥ 0 := by
          nlinarith [sq_nonneg (x * (x + y + z) - 1), sq_nonneg (y * z - 1), sq_nonneg (x * (x + y + z) - y * z), mul_pos hx (show 0 < y * z by nlinarith), mul_pos (show 0 < x * (x + y + z) by nlinarith) h6, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
        linarith 
      nlinarith
    nlinarith [h2, heq]