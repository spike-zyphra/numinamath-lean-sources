import Mathlib
/-
Let $n$ be a positive integer. Show that there exist positive integers $a$ and $b$ such that:
$$
\frac{a^{2}+a+1}{b^{2}+b+1}=n^{2}+n+1
$$
-/
theorem algebra_608034 (n : ℤ) (hz : n > 0) : ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ (((a : ℝ) ^ 2 + a + 1) / (b ^ 2 + b + 1) = n ^ 2 + n + 1):= by
  -- Let a = (n+1)^2 and b = n+1
  use (n + 1) ^ 2
  use (n + 1)
  constructor
  . -- Prove that a = (n+1)^2 > 0
    positivity
  .
    constructor
    . -- Prove that b = n+1 > 0
      omega
    . -- Prove the main equation
      -- First show denominator is positive
      have h1 : (n + 1) ^ 2 + (n + 1) + 1 > 0:= by positivity
      -- Simplify real number expressions
      rify at h1
      -- Simplify fraction expressions
      field_simp
      -- Normalize ring expressions to complete the proof
      ring_nf
