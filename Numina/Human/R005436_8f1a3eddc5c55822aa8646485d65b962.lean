import Mathlib
/- The equation $x^{3}-9 x^{2}+8 x+2=0$ has three real roots $p, q, r$. Find $\frac{1}{p^{2}}+\frac{1}{q^{2}}+\frac{1}{r^{2}}$. -/
theorem algebra_608286 (p q r : ℝ) (h : ∀ x : ℝ, x ^ 3 - 9 * x ^ 2 + 8 * x + 2 = (x - p) * (x - q) * (x - r)) : 1 / p ^ 2 + 1 / q ^ 2 + 1 / r ^ 2 = 25:= by

  -- Prove that none of the roots p, q, r can be zero
  have h1 : p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0:= by
    refine ⟨?_, ?_, ?_⟩
    all_goals
      by_contra H
      subst H
      specialize h 0
      ring_nf at h
      linarith

  -- Destructure the non-zero conditions for each root
  rcases h1 with ⟨h1, h2, h3⟩
  field_simp

  -- Prove three key relationships using Vieta's formulas:
  -- 1. Product of roots = -2
  -- 2. Sum of products of pairs = 8
  -- 3. Sum of roots = 9
  have h4 : (p * q * r = -2) ∧ (p * q + q * r + r * p = 8) ∧ (p + q + r = 9):= by
    have g1:= h 0
    have g2:= h 1
    have g3:= h 2
    refine ⟨?_, ?_, ?_⟩
    all_goals
      ring_nf at g1 g2 g3
      linarith

  -- Destructure the Vieta's formulas
  rcases h4 with ⟨h4, h5, h6⟩

  -- Apply algebraic transformations and substitute known values
  rw [show p ^ 2 * q ^ 2 * r ^ 2 = (p * q * r) ^ 2 by ring_nf]
  rw [show (q ^ 2 + p ^ 2) * r ^ 2 + p ^ 2 * q ^ 2 = (p * q + q * r + r * p) ^ 2 - 2 * (p + q + r) * (p * q * r) by ring_nf]
  rw [h4, h5, h6]
  ring_nf
