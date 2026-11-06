import Mathlib

/- definition of super_increasing -/
abbrev is_super_increasing (seq : Fin 5 → ℕ) : Prop := ∀ i, seq i > (∑ j : Finset.range i, seq j)

theorem number_theory_4969_1 : is_super_increasing ![3, 5, 9, 19, 40] := by native_decide

theorem number_theory_4969_2 : ¬ is_super_increasing ![2, 6, 10, 15, 36] := by native_decide

theorem number_theory_4969_3 : is_super_increasing ![3, 7, 17, 30, 59] := by native_decide

theorem number_theory_4969_4 : ¬ is_super_increasing ![11, 21, 41, 81, 151] := by native_decide