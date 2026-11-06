import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_106775 (x y : ℝ) (h : x^2 / 9 + y^2 / 4 = 1) :
    x + y ≤ sqrt 13 ∧ ∃ x y, x^2 / 9 + y^2 / 4 = 1 ∧ x + y = sqrt 13 := by
  have h1 : (x + y) ^ 2 ≤ 13 := by
    nlinarith [sq_nonneg (x - 9 / Real.sqrt 13), sq_nonneg (y - 4 / Real.sqrt 13),
      sq_nonneg (x + 9 / Real.sqrt 13), sq_nonneg (y + 4 / Real.sqrt 13),
      Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num), sq_nonneg (x * 4 - y * 9)]
  have h2 : x + y ≤ Real.sqrt 13 := by
    by_cases h_nonneg : x + y ≥ 0
    · -- If x + y ≥ 0, then we can square both sides
      have h3 : (x + y) ^ 2 ≤ (13 : ℝ) := h1
      have h4 : 0 ≤ (13 : ℝ) := by norm_num
      have h6 : (x + y) ≤ Real.sqrt 13 := by
        nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), h3]
      linarith
    · -- x + y < 0
      have h_neg : x + y < 0 := by linarith
      have h7 : Real.sqrt 13 ≥ 0 := Real.sqrt_nonneg 13
      have h8 : x + y ≤ Real.sqrt 13 := by
        linarith [show x + y < (0 : ℝ) by linarith, show 0 ≤ Real.sqrt 13 by positivity]
      linarith
  constructor
  · exact h2
  · -- Show existence of x, y that satisfies both
    use 9 / Real.sqrt 13, 4 / Real.sqrt 13
    constructor
    · -- Show that the first condition is satisfied
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    · -- Show that the second condition is satisfied
      have h_sqrt13_eq : (9 / Real.sqrt 13 + 4 / Real.sqrt 13) = Real.sqrt 13 := by
        have h13 : Real.sqrt 13 > 0 := by
          apply Real.sqrt_pos.mpr
          linarith
        field_simp
        <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
      linarith [h_sqrt13_eq]