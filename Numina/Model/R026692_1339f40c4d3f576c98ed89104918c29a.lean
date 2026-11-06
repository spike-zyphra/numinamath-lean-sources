import Mathlib

theorem algebra_313829 {f g : Polynomial ℝ} (hf : ∀ n, f.coeff n ≠ 0)
    (hg : ∀ n, g.coeff n ≠ 0) (r : ℝ) (hfg : ∀ x, g.eval x = (x - r) * f.eval x)
    (a c : ℝ) (ha : a = sSup {abs (f.coeff n) | n ∈ Finset.range (f.natDegree + 1)}) (hc : c = sSup {abs (g.coeff n) | n ∈ Finset.range (g.natDegree + 1)}) :
    a / c ≤ f.natDegree + 1 := by
  -- The proof idea is to observe that assumptions about non-zero coefficients can lead to bi-contradiction about the coefficients of a polynomial, since any polynomial would have infinitely many zero coefficients.
  have h1 := hf (f.natDegree + 1)
  have h2 : f.coeff (f.natDegree + 1) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    all_goals
      simp
  contradiction