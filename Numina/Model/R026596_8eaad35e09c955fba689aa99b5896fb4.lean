import Mathlib

open Nat

def Euclid (n : ℕ) := ∏ i ∈ Finset.range n, (i + 1)

theorem number_theory_206852 :
    ∀ p, Nat.Prime p → ∃ n, p ∣ Euclid n := by
  intro p hp
  use p
  have h1 : p ∣ Euclid p := by 
    have h2 : Euclid p = (p).factorial := by
      simp [Euclid, Finset.prod_range_succ, Nat.factorial]
      <;> ring
    rw [h2]
    apply Nat.dvd_factorial
    all_goals linarith [Nat.Prime.one_lt hp]
  exact h1