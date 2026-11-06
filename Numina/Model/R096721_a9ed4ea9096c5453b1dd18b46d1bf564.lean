import Mathlib

theorem number_theory_50133 :
    ∑ x in (Finset.Ico 1 100).filter (fun x => (x ^ 2 - x - 6).divisors.card = 4), x = 9 := by
  native_decide