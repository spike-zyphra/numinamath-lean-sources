import Mathlib

/- Definition of mutually relative prime, same as in Problem 4517 and 4518. -/
def MutuallyRelativePrime3 (s : Finset ℕ) := s.gcd id = 1

/- The solution set -/
def S_4522 : Finset ℕ := {66, 105, 70}

/- Find three mutually relatively prime integers from among the integers 66, 105, 42, 70, and 165. -/
theorem number_theory_4522 : S_4522 ⊆ {66, 105, 42, 70, 165} ∧ MutuallyRelativePrime3 S_4522 := by
  simp [S_4522, MutuallyRelativePrime3]
  decide
