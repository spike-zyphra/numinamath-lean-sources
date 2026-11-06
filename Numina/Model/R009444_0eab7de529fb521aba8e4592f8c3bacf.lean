import Mathlib

theorem number_theory_23375 :
    ∑ n in (Nat.divisors 144).filter (fun x => x ∈ Finset.Icc 10 99), n = 226 := by
  native_decide