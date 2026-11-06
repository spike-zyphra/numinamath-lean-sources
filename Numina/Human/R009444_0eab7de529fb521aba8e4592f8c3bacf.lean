import Mathlib

/- What is the sum of all the distinct positive two-digit factors of 144? -/
theorem number_theory_23375 :
    ∑ n in (Nat.divisors 144).filter (fun x => x ∈ Finset.Icc 10 99), n = 226 := by
  rfl