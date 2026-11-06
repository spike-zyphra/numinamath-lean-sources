import Mathlib

theorem number_theory_15019 : (∏ i ∈ (Finset.Ico 1 24).filter (fun x => Nat.Coprime x 24), i) % 24 = 1 := by 
  native_decide