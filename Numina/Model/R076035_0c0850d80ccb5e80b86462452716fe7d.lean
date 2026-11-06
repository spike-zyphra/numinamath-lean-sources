import Mathlib

theorem number_theory_50928 (s : Finset ℕ) (hs : s.card = 15) (hs1 : ∀ x ∈ s, x ≠ 0) (hs2 : ∏ x ∈ s, (x + 1) = 2015 * ∏ x ∈ s, x) : True := by 
  trivial