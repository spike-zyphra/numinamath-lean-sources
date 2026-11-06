import Mathlib

theorem algebra_127328 (a : Fin 101 → ℝ) (ha : ∀ i, 0 < a i)
    (h : ∀ k, ∃ f : Polynomial ℝ, f.degree = 100 ∧
      ∀ i ∈ Finset.range 101, f.coeff (i + k) = a i) :
    False := by
  have h1 := h 0
  rcases h1 with ⟨f, hf1, hf2⟩
  have h2 := h 1
  rcases h2 with ⟨g, hg1, hg2⟩
  have eq1 := hf2 100 (by simp)
  simp at eq1 
  have eq2 := hg2 100 (by simp)
  simp at eq2 
  have h3 : g.coeff 101 = 0 := by
    have h4 : g.natDegree ≤ 100 := by
      rw [Polynomial.natDegree_eq_of_degree_eq_some hg1]
      all_goals 
        simp
    have h5 : g.coeff 101 = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
    exact h5 
  have h4 : a 100 = 0 := by
    linarith [eq2, h3] 
  have h5 : 0 < a 100 := ha 100
  linarith [h4, h5]