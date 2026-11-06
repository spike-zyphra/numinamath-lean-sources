import Mathlib

theorem algebra_10174 {f : ℝ → ℝ} (hf : f = fun x => 4 + 5*x^3 + 100 + 2*Real.pi*x^4 + Real.sqrt 10*x^4 + 9) :
    ∃ p : Polynomial ℝ, p.degree = 4 ∧ ∀ x, f x = p.eval x := by
  use (Polynomial.C (113 : ℝ) + Polynomial.C 5 * Polynomial.X ^ 3 + Polynomial.C (2 * Real.pi + Real.sqrt 10) * Polynomial.X ^ 4)
  constructor
  · -- Compute the degree of the polynomial
    compute_degree!
    <;> try { linarith [Real.pi_pos, Real.sqrt_pos.mpr (show (0 : ℝ) < 10 by norm_num : (0 : ℝ) < 10)] }
  · -- Show that for all x, f x = p.eval x
    intro x
    simp [hf, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    <;> ring
    <;> simp [Real.pi_pos]
    <;> ring