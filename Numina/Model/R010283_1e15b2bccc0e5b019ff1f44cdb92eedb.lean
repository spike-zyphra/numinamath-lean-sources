import Mathlib

theorem number_theory_53545 :
    ∑ n in (Finset.Ico 1 30).filter (fun x => 2 ∣ x ∨ 3 ∣ x ∨ 5 ∣ x), n = 315 := by
  rfl