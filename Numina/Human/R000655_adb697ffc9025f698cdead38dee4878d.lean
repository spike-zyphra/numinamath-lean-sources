import Mathlib

/- Marcelle and Jaclyn each think of a polynomial.  Each of their polynomials is monic, has degree 4, and has the same positive constant term and the same coefficient of $z$. The product of their polynomials is \[z^8 +3z^7 +z^6 +3z^5 +4z^4 +6z^3 +2z^2 +4.\]What  is the constant term of Jaclyn's polynomial? -/
theorem algebra_13698 {f g : Polynomial ℝ} (hf : f.Monic) (hg : g.Monic)
    (hfg : f.degree = 4 ∧ g.degree = 4) (hfg1 : ∃ c, f.eval 0 = c ∧ g.eval 0 = c ∧ 0 < c)
    (hfg2 : ∃ z, f.coeff 1 = z ∧ g.coeff 1 = z) (hfg3 : f * g = Polynomial.monomial 8 1 +
    3 * Polynomial.monomial 7 1 + Polynomial.monomial 6 1 + 3 * Polynomial.monomial 5 1 +
    4 * Polynomial.monomial 4 1 + 6 * Polynomial.monomial 3 1 + 2 * Polynomial.monomial 2 1 +
    4) : g.eval 0 = 2 := by
  -- notice that constant term of the product polynomial is 4.
  have h1: (f*g).eval 0 = 4 := by
    rw [hfg3]; simp
  -- and constant term of the product polynomial is product of constant term from each polynomial.
  have h2: (f*g).eval 0 = f.eval 0 * g.eval 0 := by
    exact Polynomial.eval_mul
  -- their polynomials have the same positive constant term. suppose it's c.
  rcases hfg1 with ⟨c,hc⟩
  -- thus we can solve c.
  have ceq: c = 2 := by
    have: (4:ℝ) = 2^2 := by norm_num
    rw [h1, hc.left, hc.right.left, ← pow_two, this] at h2
    have nneg2: 0 ≤ (2:ℝ) := by norm_num
    have nnegc := le_of_lt hc.right.right
    symm
    apply (sq_eq_sq nneg2 nnegc).mp h2
  -- therefore constant term of Jaclyn's polynomial is 2.
  rw [hc.right.left,ceq]