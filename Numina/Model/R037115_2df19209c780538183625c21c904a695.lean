import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_116290 :
  IsGreatest {x | ∃ a b c : ℝ, x = a * b + b * c ∧ a ^ 2 + b ^ 2 + c ^ 2 = 1} (Real.sqrt 2 / 2) := by
  constructor
  · -- Show that sqrt(2)/2 is in the set.
    use 1 / 2, Real.sqrt 2 / 2, 1 / 2
    constructor
    · -- Show that the value equals sqrt(2)/2.
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    · -- Show that a^2 + b^2 + c^2 = 1.
      have h1 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith
  · -- Show that sqrt(2)/2 is the greatest.
    intro x hx
    rcases hx with ⟨a, b, c, h_eq, h_constr⟩
    have h1 : (a * b + b * c) ≤ Real.sqrt 2 / 2 := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (b - Real.sqrt 2 / 2), sq_nonneg (a + c - Real.sqrt 2), sq_nonneg (a - c), sq_nonneg (b + Real.sqrt 2 / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith [h_eq, h1]