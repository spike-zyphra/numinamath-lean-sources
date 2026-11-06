import Mathlib

theorem number_theory_157468 {P : Polynomial ℕ} (hP : ∀ n, P.coeff n > 0)
    (a : ℕ → ℕ) (ha0 : a 0 = 0) (han : ∀ n, a (n + 1) = P.eval (a n)) :
    ∀ m k, Nat.gcd (a m) (a k) = a (Nat.gcd m k) := by
  intro m k
  have h1 := hP (P.natDegree + 1)
  have h2 : P.coeff (P.natDegree + 1) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    linarith
  linarith