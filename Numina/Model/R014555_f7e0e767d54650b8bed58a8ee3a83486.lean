import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11268 :
  IsLeast {z : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ z = x + 2 * y ∧ 1 / (2 * x + y) + 1 / (y + 1) = 1} (Real.sqrt 3 + 1 / 2) := by
  constructor
  · -- Show that sqrt 3 + 1/2 is in the set.
    use (1 / 2 + Real.sqrt 3 / 3), (Real.sqrt 3 / 3)
    constructor
    · -- Show x > 0
      nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    constructor
    · -- Show y > 0
      nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    constructor
    · -- Show sqrt 3 + 1/2 = x + 2 * y
      nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    · -- Show 1 / (2 * x + y) + 1 / (y + 1) = 1
      have h1 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
      have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      field_simp [h1, h2]
      <;> nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), h2, Real.sqrt_nonneg 3]
  · -- Show that the value is minimal
    intro z h
    rcases h with ⟨x, y, hx, hy, h_eq, h_eq1⟩

    have h5 : 2*x + 2*y + 1 = (2*x + y)*(y + 1) := by 
      have h6 : 1 / (2*x + y) + 1 / (y + 1) = 1 := h_eq1
      have h7 : (2*x + y) > 0 := by nlinarith
      have h8 : (y + 1) > 0 := by nlinarith
      have h9 : (2*x + y) ≠ 0 := by linarith
      have h10 : (y + 1) ≠ 0 := by linarith
      field_simp [h9, h10] at h6 ⊢
      nlinarith [h6, mul_pos hx hy, sq_nonneg (x - (1 / 2 + Real.sqrt 3 / 3)), sq_nonneg (y - Real.sqrt 3 / 3), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

    have h5' : z ≥ Real.sqrt 3 + 1 / 2 := by
      have h5' : x + 2 * y ≥ Real.sqrt 3 + 1 / 2 := by
        nlinarith [sq_nonneg (x - (1 / 2 + Real.sqrt 3 / 3)), sq_nonneg (y - Real.sqrt 3 / 3), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), mul_pos hx hy, sq_pos_of_pos hx, sq_pos_of_pos hy]
      linarith [h_eq, h5']
    linarith