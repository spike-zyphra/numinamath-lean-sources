import Mathlib

theorem number_theory_156439 : ∑ x in (Finset.Ico 1 200).filter (fun y => Nat.Coprime y 200), x = 8000 := by
  native_decide