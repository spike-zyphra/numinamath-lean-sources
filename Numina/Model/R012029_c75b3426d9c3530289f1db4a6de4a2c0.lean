import Mathlib

open Polynomial Complex

theorem algebra_170201 :
    ∃ a b : ℝ, ∃ x : ℂ, x ∉ Set.range ofReal ∧ x ^ 3 = 343 ∧ x ^ 2 + a * x + b = 0 := by
  use 7, 49
  use (-7 / 2 + (7 * Real.sqrt 3 / 2) * I)
  constructor
  · -- Show x is non-real
    intro h
    rcases h with ⟨y, hy⟩
    norm_num [Complex.ext_iff] at hy 
    all_goals 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  constructor
  · -- Show x^3 = 343
    simp [pow_three]
    field_simp [Complex.ext_iff, pow_two, pow_three, mul_add, add_mul, mul_comm, mul_assoc]
    <;> ring_nf 
    <;> norm_num [Real.sqrt_sq, pow_two]
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
  · -- Show x^2 + 7 * x + 49 = 0
    simp [pow_two, Complex.ext_iff]
    field_simp [Complex.ext_iff, pow_two, mul_add, add_mul, mul_comm, mul_assoc]
    <;> ring_nf 
    <;> norm_num [Real.sqrt_sq, pow_two]
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]