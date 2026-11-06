import Mathlib

theorem number_theory_107032 :
    ∑ n in (Finset.Icc 100 999).filter (fun n => ∀ d ∈ Nat.digits 10 n, Odd d), n = 69375 := by
  native_decide