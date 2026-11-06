import Mathlib

/-Find the sum of the digits of $11 \cdot 101 \cdot 111 \cdot 110011$.-/
theorem number_theory_609813 : (Nat.digits 10 ((11 * 101 * 111 * 110011))).sum = 48 := by norm_num