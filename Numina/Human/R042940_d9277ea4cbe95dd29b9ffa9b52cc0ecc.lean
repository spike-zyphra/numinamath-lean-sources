import Mathlib

/- Find the product of $315_6 \cdot 4_6$.  Express your answer in base 6. -/
theorem number_theory_22838 : (Nat.ofDigits 6 [5, 1, 3]) * (Nat.ofDigits 6 [4]) = Nat.ofDigits 6 [2, 1, 1, 2] := by
  norm_num [Nat.ofDigits]