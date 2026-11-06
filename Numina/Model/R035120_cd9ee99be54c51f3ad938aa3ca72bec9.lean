import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_11240 {f : ℝ → ℝ} (hf : f = λ x => (m * x - n) / x - log x)
  (h : deriv f 2 = 1) : n = 6 := by
  have eqn1 : deriv f 2 = (n / (2 ^ 2) ) - (1 / 2) := by
    rw [hf]
    simp [deriv_sub, deriv_div, deriv_mul, deriv_id'', mul_comm m, mul_assoc, deriv_log, deriv_const, deriv_id', sub_eq_add_neg, add_left_comm, mul_assoc]
    all_goals field_simp [show (2 : ℝ) ≠ 0 by norm_num]
    <;> ring
    all_goals norm_num
  rw [eqn1] at h
  have eqn2 : (n / (2 ^ 2 : ℝ) ) - (1 / 2) = 1 := by
    linarith [h]
  have eqn3 : (n : ℝ) = 6 := by
    field_simp at eqn2
    linarith
  linarith [eqn3]