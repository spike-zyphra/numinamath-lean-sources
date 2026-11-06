import Mathlib

open Polynomial

theorem algebra_21918 {p : Polynomial ℝ} (h : ∀ x, (x^2 - 3 * x + 5) * p.eval x = x^4 - 3 * x^3 + 15 * x - 25) :
    p = X ^ 2 - 5 := by
  have eq2a : ∀ x : ℝ, (x^2 - 3 * x + 5) * p.eval x = x^4 - 3 * x^3 + 15 * x - 25 := by
    intro x
    specialize h x
    simpa using h
  have eq3a : ∀ x : ℝ, p.eval x = x ^ 2 - 5 := by
    intro x
    have eq3b : (x ^ 2 - 3 * x + 5) * p.eval x = x^4 - 3 * x ^ 3 + 15 * x - 25 := by
      apply eq2a
    -- To solve for p(x), need to show that (x^2 - 3 x + 5) is non-zero
    have h2 : x ^ 2 - 3 * x + 5 ≠ 0 := by 
      nlinarith [sq_nonneg (x - 3 / 2)]
    have eq4a : p.eval x = x ^ 2 - 5 := by
      apply (mul_left_inj' h2).mp
      nlinarith [sq_nonneg (p.eval x - (x ^ 2 - 5)), sq_nonneg (x ^ 2 - 5), sq_nonneg (x * (p.eval x)), sq_nonneg ((x - 3 / 2)), sq_nonneg ((p.eval x)), sq_nonneg ((x ^ 2 - 5) * x)]
    exact eq4a
  apply Polynomial.funext
  intro x
  have eq3 := eq3a x
  simp [eq3]
  <;> nlinarith [eq3a x]