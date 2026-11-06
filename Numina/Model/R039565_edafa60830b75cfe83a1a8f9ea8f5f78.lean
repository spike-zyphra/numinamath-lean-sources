import Mathlib

theorem number_theory_110265 (a : ℕ → ℕ) (ha : ∀ n, a n = a (n - 1) - 3) (ha0 : a 0 = 26) :
    a 1 = 23 ∧ ∑ i in Finset.range 20, a i = 610 ∧ ¬∃ n, ∃ m, a n = m ^ 2 := by 
  have h0 := ha 0 
  simp [ha0] at h0 
  all_goals omega