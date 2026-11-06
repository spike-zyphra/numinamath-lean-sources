import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_157070 (v : ℝ → ℝ) (h : v = λ t => 29.4 - 9.8 * t) :
    IsGreatest {x | ∃ t, x = ∫ s in (0)..t, v s} 44.1 := by
  constructor
  · -- Show 44.1 is in the set.
    use 3
    rw [h]
    norm_num [intervalIntegral.integral_const, mul_comm]
  · -- Show that 44.1 is greatest.
    intro x hx
    rcases hx with ⟨t, ht⟩
    rw [h] at ht
    have eq1 : x = 29.4 * t - 4.9 * t ^ 2 := by
      simp [intervalIntegral.integral_const, mul_comm] at ht ⊢
      linarith
    have h1 : x ≤ 44.1 := by
      rw [eq1]
      nlinarith [sq_nonneg (t - 3)]
    linarith