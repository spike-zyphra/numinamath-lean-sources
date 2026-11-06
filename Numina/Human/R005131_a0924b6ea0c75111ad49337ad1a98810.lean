import Mathlib


--Let $A=1 \cdot 4 \cdot 7 \cdot \ldots \cdot 2014$ be the product of the numbers less or equal to 2014 that give remainder 1 when divided by 3 . Find the last non-zero digit of $A$.

/-- The product of all numbers ≤ 2014 that give remainder 1 when divided by 3 -/
def A : ℕ := ∏ k ∈ Finset.range 672, (3 * k + 1)

/-- Function to find the last non-zero digit of a natural number -/
def lastNonZeroDigit (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    let digits := Nat.digits 10 n
    let nonZeroDigit := digits.find? (· ≠ 0)
    nonZeroDigit.getD 0


theorem number_theory_605694 : lastNonZeroDigit A = 2 := by
  native_decide
