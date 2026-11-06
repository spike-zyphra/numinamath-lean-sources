import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_112623 {f : ℝ → ℝ} (hf : f = λ x => log (2 + 3 * x) - 3 / 2 * x ^ 2)
  (a : ℝ) (ha : ∀ x ∈ Icc (1 / 6) (1 / 3), |a - log x| + log (deriv f x + 3 * x) > 0) :
  a ≠ log (1 / 3) := by
    by_contra h
    rw [h] at ha
    have h1 := ha (1 / 3) (by norm_num)
    have deriv_f : deriv f (1 / 3) = 0 := by
      rw [hf]
      simp [deriv_sub, deriv_mul, deriv_id', mul_comm]
      all_goals norm_num [deriv_log, deriv_const, mul_comm]
      all_goals norm_num
    have h2 : log (deriv f (1 / 3) + 3 * (1 / 3)) = log 1 := by
      rw [deriv_f]
      norm_num
    have h3 : log (deriv f (1 / 3) + 3 * (1 / 3)) = 0 := by
      rw [h2]
      norm_num
    have h4 : |log (1 / 3) - log (1 / 3)| = 0 := by 
      simp
    linarith [h4, h3]