import Mathlib

theorem number_theory_139221 {P : Polynomial ℤ} (hP : ∀ n, P.coeff n > 0)
    (a : ℕ → ℤ) (ha0 : a 0 = 0) (han : ∀ n, a (n + 1) = P.eval (a n)) :
    ∀ m k, Int.gcd (a m) (a k) = a (Int.gcd m k) := by 
  have h1 := hP (P.natDegree + 1)
  have h2 : P.coeff (P.natDegree + 1) = 0 := by 
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    linarith
  linarith