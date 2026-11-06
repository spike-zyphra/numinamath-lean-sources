import Mathlib

theorem number_theory_43349 :
    IsSquare (∏ n ∈ (Finset.Ico 1 100).filter (fun n => n.divisors.card = 3), n) := by
  native_decide