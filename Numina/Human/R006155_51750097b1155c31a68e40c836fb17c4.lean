import Mathlib

open Real Int

theorem algebra_624715 :
    ∃ k : ℕ,
      0 < (5 * k : ℝ) / 6 - ⌊(5 * k : ℝ) / 6⌋ ∧
      (5 * k : ℝ) / 6 - ⌊(5 * k : ℝ) / 6⌋ < 1 / 3 ∧
      ⌊(5 * k : ℝ) / 6⌋ = 4 := by
  -- Choose k = 5
  use 5

  -- Define the real value x representing the number of products B has completed at the moment A finishes 5
  let x : ℝ := (5 * 5 : ℝ) / 6

  -- Prove that the fractional part of x is greater than 0
  constructor
  · norm_num  -- 25 / 6 - floor(25 / 6) = 1/6 > 0

  -- Prove that the fractional part of x is less than 1/3
  constructor
  · norm_num  -- 1/6 < 1/3

  -- Prove that the integer part (floor) of x equals 4
  · norm_num  -- floor(25 / 6) = 4
