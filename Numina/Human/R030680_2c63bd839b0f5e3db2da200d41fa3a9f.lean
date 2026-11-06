import Mathlib

/- definition of super_increasing -/
abbrev is_super_increasing (seq : Fin 5 → ℕ) : Prop := ∀ i, seq i > (∑ j : Finset.range i, seq j)

/-
Determine whether each of the following sequences is super-increasing. A sequence is considered super-increasing if each term is greater than the sum of all previous terms. The sequences to evaluate are:
a) $(3,5,9,19,40)$
-/
theorem number_theory_4969_1 : is_super_increasing ![3, 5, 9, 19, 40] := by native_decide

/-
Determine whether each of the following sequences is super-increasing. A sequence is considered super-increasing if each term is greater than the sum of all previous terms. The sequences to evaluate are:
b) $(2,6,10,15,36)$
-/
theorem number_theory_4969_2 : ¬ is_super_increasing ![2, 6, 10, 15, 36] := by native_decide

/-
Determine whether each of the following sequences is super-increasing. A sequence is considered super-increasing if each term is greater than the sum of all previous terms. The sequences to evaluate are:
c) $(3,7,17,30,59)$
-/
theorem number_theory_4969_3 : is_super_increasing ![3, 7, 17, 30, 59] := by native_decide

/-
Determine whether each of the following sequences is super-increasing. A sequence is considered super-increasing if each term is greater than the sum of all previous terms. The sequences to evaluate are:
d) $(11,21,41,81,151)$.
-/
theorem number_theory_4969_4 : ¬ is_super_increasing ![11, 21, 41, 81, 151] := by native_decide
