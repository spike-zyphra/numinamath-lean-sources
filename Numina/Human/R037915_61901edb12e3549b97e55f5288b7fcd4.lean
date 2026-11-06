import Mathlib
open Polynomial
/- Find three different polynomials $P(x)$ with real coefficients such that $P\left(x^{2}+1\right)=P(x)^{2}+1$ for all real $x$.

Answer: For example, $P(x)=x, P(x)=x^{2}+1$ and $P(x)=x^{4}+2 x^{2}+2$. -/
theorem algebra_239179 : ∃ P1 P2 P3 : ℝ[X], P1 ≠ P2 ∧ P2 ≠ P3 ∧ P3 ≠ P1 ∧ (∀ x : ℝ, P1.eval (x ^ 2 + 1) = P1.eval x ^ 2 + 1) ∧ (∀ x : ℝ, P2.eval (x ^ 2 + 1) = P2.eval x ^ 2 + 1) ∧ (∀ x : ℝ, P3.eval (x ^ 2 + 1) = P3.eval x ^ 2 + 1):= by
  -- Define the three polynomials: P1(x) = x, P2(x) = x^2 + 1, P3(x) = x^4 + 2x^2 + 2
  use X, X ^ 2 + 1, X ^ 4 + 2 * X ^ 2 + 2
  -- Prove six conditions: three inequalities and three functional equations
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Prove P1 ≠ P2 by contradiction
  .
    by_contra H
    replace H : (X : ℝ [X]).eval 0 = (X ^ 2 + 1).eval 0:= by rw [←H]
    simp at H
  -- Prove P2 ≠ P3 by contradiction
  .
    by_contra H
    replace H : (X ^ 2 + 1 : ℝ [X]).eval 0 = (X ^ 4 + 2 * X ^ 2 + 2 : ℝ [X]).eval 0:= by rw [H]
    simp at H
  -- Prove P3 ≠ P1 by contradiction
  .
    by_contra H
    replace H : (X ^ 4 + 2 * X ^ 2 + 2 : ℝ [X]).eval 0 = (X : ℝ [X]).eval 0:= by rw [H]
    simp at H
  -- For the remaining three goals (functional equations), simplify the expressions
  all_goals
    intro x
    simp
  -- Complete the proof using ring normalization
  ring_nf
