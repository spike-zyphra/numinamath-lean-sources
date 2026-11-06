import Mathlib

/- 552. Find all four-digit numbers that are 9 times greater than their reversals. -/
theorem number_theory_113739 :
    {Nat.ofDigits 10 [d, c, b, a] | (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (_ : a ∈ Finset.Icc 1 9) (_ : b ∈ Finset.Icc 0 9) (_ : c ∈ Finset.Icc 0 9) (_ : d ∈ Finset.Icc 1 9) (_ : Nat.ofDigits 10 [d, c, b, a] = 9 * Nat.ofDigits 10 [a, b, c, d])} = {9801} := by
  ext x
  constructor
  -- Check 9801 satisfies the condition
  swap
  {
    rintro rfl
    use 9, 8, 0, 1
    decide
  }
  -- Check every four-digit number using `native_decide`
  -- The only solution is 9801
  rintro ⟨a, b, c, d, ha, hb, hc, hd, h, rfl⟩
  simp
  revert h d
  revert c
  revert b
  revert a
  native_decide
