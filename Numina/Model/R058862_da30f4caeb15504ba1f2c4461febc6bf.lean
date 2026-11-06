import Mathlib

open Finset

theorem number_theory_77144 {d e : ℕ → ℕ}
    (hd : ∀ n, d n = (Nat.divisors n).card)
    (he : ∀ n, e n = 2000 / n) :
    ∑ i ∈ Icc 1 2000, d i = ∑ i ∈ Icc 1 2000, e i := by 
  simp [hd, he]
  <;> native_decide