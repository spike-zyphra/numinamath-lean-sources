import Mathlib

open Finset

/- Determine the number of juggling sequences of length $n$ with exactly 1 ball.
Answer: 2^n - 1. -/
theorem combinatorics_608360 (n : ℕ) : ((powerset (Ico 0 n)) \ {∅}).card = 2 ^ n - 1 := by
  have : {∅} ⊆ (powerset (Ico 0 n)) := by
    simp
  rw [card_sdiff this, card_powerset]
  simp
