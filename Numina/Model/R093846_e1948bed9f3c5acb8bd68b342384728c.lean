import Mathlib

theorem algebra_108657 {a b : ℤ} (ha : a = ⌊Real.sqrt 17 - 2⌋) (hb : b - 1 = Real.sqrt 9)
    (h : |a - b| = b - a) : a + b = 6 := by
  -- We need to determine the integer part of sqrt(17) - 2
  have h1 : a = 2 := by
    rw [ha]
    have h2 : 4 < Real.sqrt 17 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h3 : Real.sqrt 17 < 5 := by
      rw [Real.sqrt_lt] <;> norm_num
    -- From 4 < sqrt(17) < 5, we derive 2 < sqrt(17) - 2 < 3
    have h4 : 2 < Real.sqrt 17 - 2 := by
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
    have h5 : Real.sqrt 17 - 2 < (3 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  -- Real.sqrt 9 is equal to 3 because 9 is a perfect square
  have h6 : Real.sqrt 9 = (3 : ℝ) := by
    rw [Real.sqrt_eq_cases]
    norm_num
  -- Given b - 1 = Real.sqrt 9, we can deduce b = 4
  have h7 : (b : ℝ) - 1 = (3 : ℝ) := by
    rw [h6] at hb
    exact_mod_cast hb
  have h8 : b = 4 := by
    have h9 : (b : ℝ) = (4 : ℝ) := by
      linarith
    exact_mod_cast h9
  -- With a = 2 and b = 4, we need to verify |a - b| = b - a|
  rw [h1, h8] at h
  norm_num [abs_of_nonneg, abs_of_nonpos] at h
  -- Final calculation of a + b
  linarith [h1, h8]