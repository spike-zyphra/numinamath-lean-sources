import Mathlib

/- 31. Prove that a three-digit number, in which all digits are the same, in its prime factorization contains the number 37. -/
theorem number_theory_233634 (a : ℕ) (ha : a ∈ Finset.Ico 1 10) :
    37 ∈ (Nat.ofDigits 10 [a, a, a]).primeFactors := by
  -- Simplify the expression
  simp [Nat.ofDigits] at ha ⊢
  norm_num
  omega
