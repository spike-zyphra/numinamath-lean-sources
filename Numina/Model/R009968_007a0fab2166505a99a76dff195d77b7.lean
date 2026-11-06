import Mathlib

theorem algebra_14500 {roundness : ℕ → ℕ}
    (h : roundness = fun n => ∑ p in n.primeFactors, (Nat.factorization n p))
    : roundness 1000000 = 12 := by
  rw [h]
  native_decide