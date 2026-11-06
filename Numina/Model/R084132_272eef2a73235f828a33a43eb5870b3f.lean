import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_124586 (f : ℝ → ℝ) (hf : f = λ x => x - x^3) (x0 : ℝ) (hx0 : x0 = -1) :
    ∃ m, m = -1 / deriv f x0 ∧ ∀ x, x / 2 + 1 / 2 = m * (x - x0) := by
  use 1 / 2
  constructor
  · -- Show m = -1 / deriv f x0
    have h1 : deriv f x0 = -2 := by
      rw [hf]
      simp [deriv_sub, deriv_id'', deriv_pow, mul_comm]
      rw [hx0]
      norm_num
      all_goals norm_num [deriv_id'', deriv_pow, mul_comm]
      all_goals norm_num
    rw [h1]
    norm_num
    <;> field_simp
    <;> norm_num
  · -- Show that x / 2 + 1 / 2 = m * (x - x0) for all x
    intro x
    rw [hx0]
    ring_nf
    <;> field_simp
    <;> ring