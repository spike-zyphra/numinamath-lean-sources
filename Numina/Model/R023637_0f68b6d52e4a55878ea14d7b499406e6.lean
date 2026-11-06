import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_155717 (f : ℝ → ℝ) (hf : f = λ x => 4 * x ^ 2 - 6 * x + 3)
  (x1 x2 : ℝ) (hx1 : deriv f x1 = 2) (hx2 : deriv f x2 = -4) :
  (x1, f x1) = (1, 1) ∧ (x2, f x2) = (1 / 4, 7 / 4) := by 
  have hf1 : ∀ x, deriv f x = 8 * x - 6 := by
    intro x
    rw [hf]
    simp [deriv_pow, deriv_sub, deriv_add, deriv_const, mul_comm]
    <;> field_simp
    <;> ring_nf
  have eq1 : deriv f x1 = 8 * x1 - 6 := hf1 x1
  have eq_x1 : 8 * x1 - 6 = 2 := by
    linarith [hx1, eq1]
  have hx1_val : x1 = 1 := by
    linarith
  have hf11 : f x1 = 1 := by 
    rw [show x1 = 1 by linarith [hx1_val]]
    norm_num [hf]
  have eq2 : deriv f x2 = 8 * x2 - 6 := hf1 x2
  have eq_x2 : 8 * x2 - 6 = -4 := by
    linarith [hx2, eq2]
  have hx2_val : x2 = 1 / 4 := by
    linarith
  have hf22 : f x2 = 7 / 4 := by 
    rw [show x2 = 1 / 4 by linarith [hx2_val]]
    norm_num [hf]
  constructor
  · -- Show (x1, f x1) = (1, 1)
    apply Prod.ext
    · exact hx1_val
    · exact hf11
  · -- Show (x2, f x2) = (1 / 4, 7 / 4)
    apply Prod.ext
    · exact hx2_val
    · exact hf22