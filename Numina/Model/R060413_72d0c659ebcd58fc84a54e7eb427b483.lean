import Mathlib

theorem number_theory_322047 {A : Finset ℕ} (hA : A = (Nat.divisors 12)) :
    ∑ x ∈ A, (ArithmeticFunction.moebius x) = 0 := by 
  rw [hA]
  native_decide