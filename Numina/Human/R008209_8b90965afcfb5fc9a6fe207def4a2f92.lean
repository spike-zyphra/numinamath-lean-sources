import Mathlib

/- Let $P(x) = x^2 + rx + s$ be a quadratic polynomial with real coefficients. Suppose $P(x)$ has two distinct real roots, both of which are less than $-1$, and the difference between the two roots is less than $2$. Prove that $P(P(x)) > 0$ for all real $x$. -/
theorem algebra_618821 {r s : ℝ} {P : ℝ → ℝ} (hp : P = fun x => x ^ 2 + r * x + s)
    (hroots : ∃ x y, x ≠ y ∧ x < -1 ∧ y < -1 ∧ P x = 0 ∧ P y = 0 ∧ |x - y| < 2) :
    ∀ x, P (P x) > 0 := by
  -- Extract the two roots x and y from the hypothesis
  rcases hroots with ⟨x, y, hxy, hx1, hy1, hPx, hPy, hxy2⟩
  -- Rename some of the hypotheses for clarity
  have h3 : P x = 0 := hPx
  have h4 : P y = 0 := hPy
  have h5 : |x - y| < 2 := hxy2

  -- Express that x is a root of P in algebraic form
  have eq1 : x^2 + r * x + s = 0 := by
    rw [hp] at h3
    simpa using h3

  -- Express that y is a root of P in algebraic form
  have eq2 : y^2 + r * y + s = 0 := by
    rw [hp] at h4
    simpa using h4

  -- Prove that the sum of roots equals -r (Vieta's formula)
  have h_sum : x + y = -r := by
    have h : x^2 + r * x + s - (y^2 + r * y + s) = 0 := by linarith
    have h' : (x - y) * (x + y + r) = 0 := by
      ring_nf at h ⊢
      linarith
    cases' (mul_eq_zero.mp h') with h1 h2
    · -- x - y = 0, but x ≠ y
      exfalso
      exact hxy (by linarith)
    · -- x + y + r = 0
      linarith

  -- Prove that the product of roots equals s (Vieta's formula)
  have h_prod : x * y = s := by
    nlinarith [sq_nonneg (x - y), eq1, eq2, h_sum]

  -- Show that the square of the difference between roots is less than 4
  have h6 : (x - y) ^ 2 < 4 := by
    have h1 : (x - y) ^ 2 < 4 := by
      cases abs_cases (x - y) with
      | inl h2 => nlinarith
      | inr h2 => nlinarith
    linarith

  -- Derive a bound on the discriminant r^2 - 4s
  have h7 : r^2 - 4 * s < 4 := by
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), h_sum, h_prod, h6]

  -- Begin the main proof for an arbitrary x
  intro x

  -- Prove that P(x) > -1 for all x
  have hQ : P x > -1 := by
    have h : x^2 + r * x + s + 1 > 0 := by
      nlinarith [sq_nonneg (x + r / 2), sq_nonneg (x - y), sq_nonneg (r), sq_nonneg (s),
        h_sum, h_prod, h7]
    have h2 : P x > -1 := by
      rw [hp]
      simp
      linarith
    exact h2

  -- Prove that P(P(x)) > 0 by contradiction
  have hPP : P (P x) > 0 := by
    by_contra h
    push_neg at h
    have h4 : P (P x) ≤ 0 := by linarith
    have h5 : P (P x) = (P x) ^ 2 + r * (P x) + s := by
      rw [hp]
    rw [h5] at h4
    nlinarith [sq_nonneg (P x - x), sq_nonneg (P x - y), hQ, eq1, eq2, h_sum, h_prod]

  -- Return the final result
  exact hPP
