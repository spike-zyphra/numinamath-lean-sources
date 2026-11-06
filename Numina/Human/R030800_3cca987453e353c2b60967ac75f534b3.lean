import Mathlib

/-A number is chosen at random from the set of consecutive natural numbers $\{1, 2, 3, \ldots, 24\}$. What is the probability that the number chosen is a factor of $4!$? Express your answer as a common fraction.-/
theorem probability_16042 : {x | x ∈ Finset.Icc 1 24 ∧ x ∣ Nat.factorial 4}.ncard / 24 = 1 / 3 := by
  -- The number $4! = 24$ has prime factorization $2^3 * 3^1$.
  have : Nat.factorial 4 = 24 := by norm_cast
  rw [this]
  have : {x | x ∈ Finset.Icc 1 24 ∧ x ∣ 24} = Nat.divisors 24 := by
    ext x
    simp [Nat.divisors]
    intro _ _
    constructor
    repeat . intro h
             linarith
  rw [this]
  norm_cast
