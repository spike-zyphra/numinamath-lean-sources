import Mathlib

/- The ''roundness'' of an integer greater than 1 is the sum of the exponents of the prime factorization of the number. For example, $20 = 2^2 \times 5^1$, so 20 has a roundness of 3. What is the roundness of 1,000,000? -/
theorem algebra_14500 {roundness : ℕ → ℕ}
    (h : roundness = fun n => ∑ p in n.primeFactors, (Nat.factorization n p))
    : roundness 1000000 = 12 := by
  rw [h]
  native_decide