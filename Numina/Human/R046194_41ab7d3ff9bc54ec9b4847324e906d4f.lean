import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_315292 (a b : ℝ) (ha : abs a < 1) (hb : abs b < 1) :
    abs (a * b + sqrt ((1 - a^2) * (1 - b^2))) ≤ 1 ∧
    abs (a * b - sqrt ((1 - a^2) * (1 - b^2))) ≤ 1 := by
  have h1 : -1 < a := by linarith [abs_lt.mp ha]
  have h2 : a < 1 := by linarith [abs_lt.mp ha]
  have h3 : -1 < b := by linarith [abs_lt.mp hb]
  have h4 : b < 1 := by linarith [abs_lt.mp hb]

  have h5 : 0 ≤ sqrt ((1 - a^2) * (1 - b^2)) := sqrt_nonneg ((1 - a^2) * (1 - b^2))
  have h6 : 0 ≤ 1 - a^2 := by
    have : a^2 ≤ 1 := by nlinarith
    linarith
  have h7 : 0 ≤ 1 - b^2 := by
    have : b^2 ≤ 1 := by nlinarith
    linarith
  have h8 : 0 ≤ (1 - a^2) * (1 - b^2) := mul_nonneg h6 h7
  constructor
  · -- We need to prove |ab + sqrt((1 - a^2)(1 - b^2))| ≤ 1
    have h9 : -1 ≤ a * b + sqrt ((1 - a^2) * (1 - b^2)) := by
      nlinarith [Real.sq_sqrt h8, mul_self_nonneg (a - b), mul_self_nonneg (a + b)]
    have h10 : a * b + sqrt ((1 - a^2) * (1 - b^2)) ≤ 1 := by
      nlinarith [Real.sq_sqrt h8, mul_self_nonneg (a - b), mul_self_nonneg (a + b)]
    apply abs_le.mpr
    constructor <;> linarith
  · -- We need to prove |ab - sqrt((1 - a^2)(1 - b^2))| ≤ 1
    have h11 : -1 ≤ a * b - sqrt ((1 - a^2) * (1 - b^2)) := by
      nlinarith [Real.sq_sqrt h8, mul_self_nonneg (a - b), mul_self_nonneg (a + b)]
    have h12 : a * b - sqrt ((1 - a^2) * (1 - b^2)) ≤ 1 := by
      nlinarith [Real.sq_sqrt h8, mul_self_nonneg (a - b), mul_self_nonneg (a + b)]
    apply abs_le.mpr
    constructor <;> linarith