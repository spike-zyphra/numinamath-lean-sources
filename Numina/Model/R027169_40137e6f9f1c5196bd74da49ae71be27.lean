import Mathlib

theorem algebra_141725 {p : Polynomial ℤ} (hp : p.degree = 32)
    (h1 : p.coeff 1 = -2) (h2 : ∀ i ∈ Finset.Icc 2 32, p.coeff i = 0) :
    p.coeff 32 = 2^27 - 2^11 := by
  have h3 := h2 32 (by simp)
  have h33 : p.natDegree = 32 := by
    rw [Polynomial.natDegree_eq_of_degree_eq_some hp]
  have h34 : p.coeff 32 = 0 := h3 
  have h35 : p.leadingCoeff = 0 := by
    have h36 : p.leadingCoeff = p.coeff 32 := by 
      rw [Polynomial.leadingCoeff, h33]
    rw [h36, h34]
  have h38 : p ≠ 0 := by 
    intro h
    rw [h] at hp
    simp at hp
  have h39 : p.leadingCoeff ≠ 0 := by
    have n1 : p ≠ 0 := h38 
    have hn1 : p.leadingCoeff ≠ 0 := by 
      apply Polynomial.leadingCoeff_ne_zero.mpr
      exact h38
    exact hn1
  contradiction