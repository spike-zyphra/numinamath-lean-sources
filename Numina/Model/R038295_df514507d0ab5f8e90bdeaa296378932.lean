import Mathlib

theorem number_theory_31595 {p q : ℕ} (P Q : Polynomial ℤ) (hP : P.degree = p) (hQ : Q.degree = q)
    (hPQ : P ∣ Q) (hPcoeff : ∀ n, P.coeff n = 1 ∨ P.coeff n = 2002) (hQcoeff : ∀ n, Q.coeff n = 1 ∨ Q.coeff n = 2002) :
    (p + 1) ∣ (q + 1) := by 
  have h3 := hPcoeff (P.natDegree + 1)
  have h01 : P.coeff (P.natDegree + 1) = 0 := by
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    simp
  cases h3 with
  | inl h1l =>
    nlinarith [h01, h1l]
  | inr h1r =>
    nlinarith [h01, h1r]