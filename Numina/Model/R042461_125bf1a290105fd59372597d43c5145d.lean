import Mathlib

theorem number_theory_31905 {P : Polynomial ℕ} (hP : P.degree = 699)
    (hP1 : ∀ n, P.coeff n > 0) (hP2 : P.eval 1 ≤ 2022) :
    ∃ k, ∃ m, ∑ i ∈ Finset.range m, P.coeff (k + i) = 22 ∨
      ∑ i ∈ Finset.range m, P.coeff (k + i) = 55 ∨
      ∑ i ∈ Finset.range m, P.coeff (k + i) = 77 := by 
  have h1 := hP1 700
  have h2 : P.coeff 700 = 0 := by
    have h1 : P.degree = 699 := hP
    have h5 : Polynomial.natDegree P = 699 := by
      rw [Polynomial.natDegree_eq_of_degree_eq_some h1]
      all_goals omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show 700 > P.natDegree by
      omega
    )]
    all_goals omega
  linarith