import Mathlib

/- The integers 195 and 61 are expressed in base 4 and added.  What is the resulting sum, expressed in base 4? -/
theorem number_theory_11989 : (Nat.digits 4 (195 + 61)) = [0, 0, 0, 0, 1] := by
  native_decide
