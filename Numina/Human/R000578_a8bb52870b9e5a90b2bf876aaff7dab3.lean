import Mathlib

/-Expand $-(3-c)(c+2(3-c))$. What is the sum of the coefficients of the expanded form?-/
theorem algebra_12866 {c g : Polynomial ℝ} (hc : c = Polynomial.X) (hg : g = - (3 - c) * (c + 2 * (3 - c))) :
    ∑ n ∈ Finset.range (g.natDegree + 1), g.coeff n = -10 := by
  -- show that degree of g is 2
  have degree : g.natDegree = 2 := by
    -- first calculate the monomial of degree 2
    have degree₂ : (Polynomial.X ^ 2 : Polynomial ℝ).natDegree = 2 := by
      apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      apply Polynomial.natDegree_X_pow_le
      simp
    -- then calculate the monomial of degree 1
    have degree₁ : (Polynomial.X * 9 : Polynomial ℝ).natDegree = 1 := by
      simp
    -- add them together
    replace degree₂ : (Polynomial.X * 9 - Polynomial.X ^ 2 : Polynomial ℝ).natDegree = 2 := by
      nth_rewrite 2 [<-degree₂]
      apply Polynomial.natDegree_sub_eq_right_of_natDegree_lt
      linarith only [degree₁, degree₂]
    -- so finally we have the degree of g is 2
    rw [hg, hc]
    ring_nf
    nth_rewrite 2 [<-degree₂]
    apply Polynomial.natDegree_add_eq_right_of_natDegree_lt
    rw [degree₂]
    simp
  -- rewrite g.natDegree = 2 and expand Finset.sum
  rw [degree]
  simp [Finset.sum]
  rw [hg, hc]
  ring_nf
  rw [Polynomial.coeff_add, Polynomial.coeff_sub]
  simp
  rw [Polynomial.coeff_X]
  simp
  -- calculate each monomial's coefficient
  have coeff (n : ℕ) (hn : n ≠ 0) : Polynomial.coeff (18 : Polynomial ℝ) n = 0 := by
    apply Polynomial.coeff_C_ne_zero
    exact hn
  have coeff₂ := coeff 2 (show 2 ≠ 0 by norm_num)
  have coeff₁ := coeff 1 (show 1 ≠ 0 by norm_num)
  rw [coeff₁, coeff₂]
  norm_num
