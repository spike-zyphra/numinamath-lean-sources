import Mathlib

theorem number_theory_163383 : ∃ k, (k^2) = ∏ i ∈ Finset.Icc 1 20, if i = 10 then 1 else Nat.factorial i := by
  use (∏ i ∈ Finset.Icc 1 20, if i = 10 then 1 else Nat.factorial i).sqrt
  native_decide