import Mathlib

theorem number_theory_43694 {f g : Polynomial ℕ} (hf : f.degree > 0)
    (hg : g.degree > 0) (hfg : ∀ n, f.coeff n > 0 ∧ g.coeff n > 0)
    (m n : ℕ) :
    ∀ N, ∃ k : ℕ, k > N ∧ ∀ i ∈ Finset.Icc 0 k, ¬Prime (f.eval (m ^ n) + g.eval i) := by
  have h1 := hfg (f.natDegree + 1)
  have h2 : f.coeff (f.natDegree + 1) = 0 := by
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    all_goals
      simp
  have h3 : f.coeff (f.natDegree + 1) > 0 := h1.1
  linarith [h2, h3]