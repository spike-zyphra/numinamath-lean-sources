import Mathlib

open Topology Filter

/- 40. Prove that $\lim _{n \rightarrow+\infty} \frac{x^{n}}{n!}=0$ for any value of $x$. ${ }^{*}$ -/
theorem calculus_184908 (x : ℝ) :
    Tendsto (λ n => x^n / Nat.factorial n) atTop (𝓝 0) := by
  -- This result is already in Mathlib.
  exact FloorSemiring.tendsto_pow_div_factorial_atTop x