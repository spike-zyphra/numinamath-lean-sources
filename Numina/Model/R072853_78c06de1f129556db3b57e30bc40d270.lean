import Mathlib

open Finset

theorem number_theory_206192 {N : ℕ → ℕ}
    (hN : ∀ n, N n = (Nat.divisors n).card) :
    Even (∑ i ∈ range 1989, N (i + 1)) := by
  rw [sum_congr rfl (fun i _ => hN (i + 1))]
  native_decide