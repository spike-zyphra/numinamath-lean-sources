import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_155984 (f : ℝ → ℝ) (hf : f = λ x => 2 * x ^ 3 + 3 * x ^ 2 - 12 * x + 1) :
    ∀ x ∈ Ioo (-2) 1, deriv f x < 0 := by

  intro x hx
  have h1 : -2 < x := hx.1
  have h2 : x < 1 := hx.2
  have h3 : deriv f x = 6 * x^2 + 6 * x - 12 := by
    rw [hf]
    simp [deriv_add, deriv_sub, deriv_pow, deriv_const, deriv_id'', mul_comm]
    all_goals
      field_simp <;> 
      ring_nf <;> 
      field_simp <;> 
      ring
      <;> norm_num
      <;> ring_nf <;> 
      norm_num
      <;> norm_num
  -- $6x^2 + 6x - 12 < 0$ is equivalent to $x^2 + x - 2 < 0$ after dividing by 6.
  -- Completing the square: $6(x + 1/2)^2 - 27/2 < 0$ which is true when $x \in (-2, 1)$.
  have h4 : deriv f x = 6 * x^2 + 6 * x - 12 := h3
  rw [h4]
  -- $6x^2 + 6x - 12 < 0$ is true when $x \in (-2, 1)$ as calculated.
  have : 6 * x^2 + 6 * x - 12 < 0 := by 
    nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg ((x + 2)), sq_nonneg ((x - 1)), mul_pos (by linarith : (0 : ℝ) < 1 - x) (by linarith : (0 : ℝ) < x + 2), sq_nonneg (x * (x + 2)), sq_nonneg ((x - 1) * (x + 2)), sq_nonneg ((x + 1 / 2) * (x + 1 / 2)), sq_nonneg ((x + 1 / 2) * (x + 2)), sq_nonneg ((x + 1 / 2) * (x - 1)), mul_nonneg (show (0 : ℝ) ≤ x + 2 by linarith) (show (0 : ℝ) ≤ (1 - x) by linarith)]
  linarith