import Mathlib

theorem number_theory_137102 :
    ∑ n in (Finset.Icc 1 10000).filter (fun n => n.divisors.card = 4 ∧ ∑ d in n.divisors, d = 42), n = 26 := by
  native_decide