import Mathlib

/- A positive integer is "mild" if its base-3 representation never contains the digit 2. -/
@[reducible]
def mild (n : ℕ) :=
    0 < n ∧ 2 ∉ Nat.digits 3 n

/- Call a positive integer "mild" if its base-3 representation never contains the digit 2 . How many values of $n(1 \leq n \leq 1000)$ have the property that $n$ and $n^{2}$ are both mild? -/
theorem number_theory_611045 :
    { n ∈ Finset.Icc 1 1000 | mild n ∧ mild (n ^ 2) }.card = 7 := by
  -- We check the answer by brute force.
  native_decide
