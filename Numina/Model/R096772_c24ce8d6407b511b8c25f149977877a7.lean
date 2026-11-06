import Mathlib

theorem algebra_146325 : (|(Real.sqrt 65 - Real.sqrt 63) - 0.13| < |(Real.sqrt 65 - Real.sqrt 63) - 0.12| ∧
    |(Real.sqrt 65 - Real.sqrt 63) - 0.13| < |(Real.sqrt 65 - Real.sqrt 63) - 0.14| ∧
    |(Real.sqrt 65 - Real.sqrt 63) - 0.13| < |(Real.sqrt 65 - Real.sqrt 63) - 0.15| ∧
    |(Real.sqrt 65 - Real.sqrt 63) - 0.13| < |(Real.sqrt 65 - Real.sqrt 63) - 0.16|) := by
  have h3 : Real.sqrt 65 > Real.sqrt 63 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h4 : Real.sqrt 65 ^ 2 = 65 := Real.sq_sqrt (by norm_num)
  have h5 : Real.sqrt 63 ^ 2 = 63 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 65 - Real.sqrt 63 > 0 := by linarith [h3]
  have h7 : |(Real.sqrt 65 - Real.sqrt 63) - 0.13| < |(Real.sqrt 65 - Real.sqrt 63) - 0.12| := by
    have h8 : ((Real.sqrt 65 - Real.sqrt 63) - 0.13) ^ 2 < ((Real.sqrt 65 - Real.sqrt 63) - 0.12) ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 65 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 63 by norm_num), Real.sqrt_nonneg 65, Real.sqrt_nonneg 63, h3]
    cases' abs_cases (Real.sqrt 65 - Real.sqrt 63 - 0.13) with h h <;> cases' abs_cases (Real.sqrt 65 - Real.sqrt 63 - 0.12) with k k <;> nlinarith
  have h8 : |(Real.sqrt 65 - Real.sqrt 63) - 0.13| < |(Real.sqrt 65 - Real.sqrt 63) - 0.14| := by
    have h9 : ((Real.sqrt 65 - Real.sqrt 63) - 0.13) ^ 2 < ((Real.sqrt 65 - Real.sqrt 63) - 0.14) ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 65 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 63 by norm_num), Real.sqrt_nonneg 65, Real.sqrt_nonneg 63, h3]
    cases' abs_cases (Real.sqrt 65 - Real.sqrt 63 - 0.13) with h h <;> cases' abs_cases (Real.sqrt 65 - Real.sqrt 63 - 0.14) with k k <;> nlinarith
  have h9 : |(Real.sqrt 65 - Real.sqrt 63) - 0.13| < |(Real.sqrt 65 - Real.sqrt 63) - 0.15| := by
    have h10 : ((Real.sqrt 65 - Real.sqrt 63) - 0.13)  ^ 2 < ((Real.sqrt 65 - Real.sqrt 63) - 0.15)  ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 65 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 63 by norm_num), Real.sqrt_nonneg 65, Real.sqrt_nonneg 63, h3]
    cases' abs_cases (Real.sqrt 65 - Real.sqrt 63 - 0.13) with h h <;> cases' abs_cases (Real.sqrt 65 - Real.sqrt 63 - 0.15) with k k <;> nlinarith
  have h10 : |(Real.sqrt 65 - Real.sqrt 63) - 0.13| < |(Real.sqrt 65 - Real.sqrt 63) - 0.16| := by
    have h11 : ((Real.sqrt 65 - Real.sqrt 63) - 0.13)  ^ 2 < ((Real.sqrt 65 - Real.sqrt 63) - 0.16)  ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 65 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 63 by norm_num), Real.sqrt_nonneg 65, Real.sqrt_nonneg 63, h3]
    cases' abs_cases (Real.sqrt 65 - Real.sqrt 63 - 0.13) with h h <;> cases' abs_cases (Real.sqrt 65 - Real.sqrt 63 - 0.16) with k k <;> nlinarith
  constructor
  · exact h7
  constructor
  · exact h8
  constructor
  · exact h9
  · exact h10