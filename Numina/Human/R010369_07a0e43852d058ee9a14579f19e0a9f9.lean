import Mathlib

open Real Set
open scoped BigOperators

/-Given a quadratic equation in terms of $x$: $x^{2}+4x+k=0$ has real roots, find the range of values for $k$.-/
theorem algebra_9337 (k : ℝ) :
(∃ x : ℝ, x ^ 2 + 4 * x + k = 0) ↔ k ≤ 4 := by
-- Break "iff" and rewrite assumptions
  constructor
  · rintro ⟨x, hx⟩; rw [add_comm, ← eq_neg_iff_add_eq_zero] at hx
    rw [show -(x ^ 2 + 4 * x) = - (x + 2) ^ 2 + 4 by ring] at hx
-- Apply pow_two_nonneg and prove that $4$ is an upperbound of $k$
    have : 0 ≤ (x + 2) ^ 2 := by apply pow_two_nonneg
    linarith
-- Prove the reversed implication by finding a root of the quadratic equation
  intro hk; use sqrt (4-k)-2; ring_nf
  rw [pow_two, ← sqrt_mul, sqrt_mul_self]; ring
  linarith; linarith