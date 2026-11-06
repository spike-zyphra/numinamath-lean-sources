import Mathlib

/- An integer is randomly selected from the integers 0 through 99, inclusive. What is the probability that the integer is in the range 10 through 20, inclusive? Express your answer as a common fraction. -/
theorem algebra_19850 : (Nat.card {x : ℕ | x ∈ Finset.Icc 10 20}) / 100 = 11 / 100 := by
  simp [Finset.Icc, Nat.card]
  native_decide
