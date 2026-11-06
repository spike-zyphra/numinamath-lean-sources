import Mathlib

theorem number_theory_287749 : (∏ i in (Finset.Ico 1 100).filter (fun x => Even x ∧ ¬(10 ∣ x)), i) % 10 = 6 := by 
  native_decide