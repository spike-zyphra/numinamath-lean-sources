import Mathlib

def mark (n : ℕ) := n % 3

theorem number_theory_244225 (S : ℕ) (hS : S = ∑ i ∈ Finset.range 2019, mark (i + 1)) :
    S ≤ 2021 := by 
  rw [hS]
  native_decide