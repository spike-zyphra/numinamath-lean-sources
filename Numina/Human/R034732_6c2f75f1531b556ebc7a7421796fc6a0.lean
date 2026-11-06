import Mathlib

open Real Set
open scoped BigOperators

/-Given the function $f(x)=e^{x}+x^{3}$ (where $e$ is the base of the natural logarithm), if $f(x^{2}) < f(3x-2)$, then the range of the real number $x$ is _____.-/
theorem algebra_9382 {f : ℝ → ℝ} (hf : f = λ x => exp x + x^3) :
  {x | f (x^2) < f (3 * x - 2)} = {x | 1 < x ∧ x < 2} := by
    ext x
    --  By using the derivative to study the function's monotonicity, we find that
    -- $f(x)$ is monotonically increasing on its domain.
    have aux : StrictMono f := by
      simp [hf]
      refine StrictMono.add_monotone (exp_strictMono) ?_
      refine StrictMono.monotone ?hf
      refine Odd.strictMono_pow (by decide)
    -- Given $f(x^{2}) < f(3x-2)$, and knowing that $f(x)$ is a strictly increasing function, we can write the inequality as:
    -- $$
    -- x^{2} < 3x-2
    -- $$
    simp_rw [StrictMono.lt_iff_lt aux]
    constructor <;> intro h
    · simp at *
      -- Factoring the quadratic expression, we get:
      -- $$
      -- (x-1)(x-2) < 0
      -- $$
      have : (x - 1) * (x - 2) < 0 := by linarith
      -- Solving for $x$, we find that the inequality holds true for $1 < x < 2$.
      rcases mul_neg_iff.1 this with hl | hr
      · simp at hl; tauto
      · simp at hr; linarith
    · simp at *
      nlinarith
