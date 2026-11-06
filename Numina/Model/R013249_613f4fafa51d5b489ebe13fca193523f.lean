import Mathlib

def isGood (n : ℕ) := ∃ s : Finset ℕ, ∑ d ∈ s, d = n - 1 ∧ ∀ d ∈ s, d ∣ n ∧ d > 1

theorem number_theory_40992 (n : ℕ) :
    ∃ m, isGood (n * m) := by
  use 0
  use ∅
  constructor
  · -- The sum of elements in ∅ is 0, which equals 0 - 1
    simp
  · -- ∀ d ∈ ∅, d ∣ 0 ∧ d > 1
    intro d hd
    simp at hd
    all_goals try { tauto }