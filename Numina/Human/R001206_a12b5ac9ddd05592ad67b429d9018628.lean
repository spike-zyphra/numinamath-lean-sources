import Mathlib

/- The perfect squares from $1$ through $2500,$ inclusive, are printed in a sequence of digits $1491625\ldots2500.$ How many digits are in the sequence? -/
theorem algebra_21353 : ∑ x ∈ (Finset.Icc 1 2500).filter IsSquare, (Nat.digits 10 x).length = 157 := by native_decide
