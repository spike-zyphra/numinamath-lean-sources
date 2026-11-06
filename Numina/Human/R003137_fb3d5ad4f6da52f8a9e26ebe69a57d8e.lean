import Mathlib

open Polynomial

/- Determine the real polynomials satisfying the relation:
$$
P\left(x^{2}\right)=\left(x^{2}+1\right) P(x)
$$
 -/
theorem algebra_156438 {P : Polynomial ℝ} :
    (∀ x, P.eval (x^2) = (x^2 + 1) * P.eval x) ↔ ∃ a : ℝ, P = C a * (X^2 - 1) := by
  constructor
  -- Prove that P(x^2) = (x^2 + 1) * P(x) implies that P = a * (X^2 - 1) for some a.
  · intro hp
    -- Consider two cases: P = 0 and P ≠ 0.
    by_cases h0 : P = 0
    · use 0
      -- If P = 0 then a = 0.
      simp only [h0, map_zero, zero_mul]
    -- Assume that P ≠ 0 and show that P = a * (X^2 - 1) for some a.
    have hp' : P.comp (X ^ 2) = (X ^ 2 + 1) * P := by
      apply Polynomial.funext
      simp [hp]
    -- Show that the degree of P is 2.
    have hdeg : P.natDegree = 2 := by
      apply_fun natDegree at hp'
      -- The degree of P(X^2) is 2 * P.natDegree.
      simp [natDegree_comp] at hp'
      -- The degree of X^2 + 1 is 2.
      have h : (X ^ 2 + 1 : ℝ[X]).natDegree = 2 := by compute_degree!
      have := ne_zero_of_natDegree_gt (show 0 < (X ^ 2 + 1 : ℝ[X]).natDegree by simp [h])
      -- The degree of (X^2 + 1) * P is 2 + P.natDegree.
      rw [natDegree_mul this h0, h] at hp'
      -- We get 2 * P.natDegree = 2 + P.natDegree, so P.natDegree = 2.
      linarith
    -- P.natDegree = 2 so we can find a, b, c such that
    -- P = a * X^2 + b * X + c.
    have ⟨a, b, c, h⟩ : ∃ a b c : ℝ, P = C a * X ^ 2 + C b * X + C c := by
      rw [as_sum_range_C_mul_X_pow P]
      use P.coeff 2, P.coeff 1, P.coeff 0
      simp [hdeg, Finset.sum]
      ring
    simp [h] at hp
    -- Substitute x = 1 into hp and get a + b + c = 2 * (a + b + c).
    have hp1 := hp 1
    -- Substitute x = -1 into hp and get a + b + c = 2 * (a - b + c).
    have hp2 := hp (-1)
    norm_num at hp1 hp2
    -- It is easy to find that b = 0 and c = -a.
    have hb : b = 0 := by linarith
    have hc : c = -a := by linarith
    -- We get that P = a * X^2 - a = a * (X^2 - 1).
    use a
    simp [h, hb, hc]
    ring
  -- It is easy to show that P = a * (X^2 - 1) satisfies the required relation:
  -- P(x^2) = (x^2 + 1) * P(x).
  · intro ⟨a, hp⟩ x
    simp [hp]
    ring