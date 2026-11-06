import Mathlib

theorem algebra_308430 (x : ℝ) (hx : x = Real.sqrt 5) (y : ℤ) (hy : y = ⌊x⌋) :
    1 / (x - y) = Real.sqrt 5 + 2 := by
  have h1 : y = 2 := by
    rw [hy, hx]
    have h2 : 2 < Real.sqrt 5 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h3 : Real.sqrt 5 < 3 := by
      rw [Real.sqrt_lt] <;> norm_num
    have h4 : ⌊Real.sqrt 5⌋ = 2 := by
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> nlinarith [Real.sqrt_nonneg 5, h2, h3]
    exact h4
  rw [h1]
  rw [hx]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  field_simp [(show Real.sqrt 5 - (2 : ℝ) ≠ 0 by
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), sq_pos_of_pos (show 0 < Real.sqrt 5 by positivity)]
  )]
  <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]