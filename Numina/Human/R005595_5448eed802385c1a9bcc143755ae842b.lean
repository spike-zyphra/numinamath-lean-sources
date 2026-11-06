/-
Let $Q(x)=x^{2}+2 x+3$, and suppose that $P(x)$ is a polynomial such that

$$
P(Q(x))=x^{6}+6 x^{5}+18 x^{4}+32 x^{3}+35 x^{2}+22 x+8
$$

Compute $P(2)$.
-/
theorem polynomial_evaluation (Q : ℝ → ℝ) (Qdef : ∀ x, Q x = x^(2 : ℝ) + 2*x + 3) 
(P : ℝ → ℝ)
(Pdef : ∀ x, P (Q x) = (x^6 + 6*x^5 + 18*x^4 + 32*x^3 + 35*x^2 + 22*x + 8))
:
  P (2) = 2 := by
  have lem1 : Q (- 1) = 2 := by {
    rw [Qdef]
    ring
  }
  rw [← lem1]
  rw [Pdef]
  rw [lem1]
  ring