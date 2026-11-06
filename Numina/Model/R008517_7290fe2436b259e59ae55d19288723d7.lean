import Mathlib

theorem number_theory_172539 : ∑ n in (Finset.Ico 1 1980).filter (fun n => Even (Nat.digits 10 n).sum), n = 979605 := by
  native_decide