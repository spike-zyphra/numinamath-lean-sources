import Mathlib

theorem number_theory_154264 : ∑ n in (Finset.Ico 1 233).filter (fun x => Even x ∧ ¬10 ∣ x), n = 10812 := by
  native_decide