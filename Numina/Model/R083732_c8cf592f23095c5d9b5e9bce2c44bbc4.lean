import Mathlib

theorem number_theory_117594 (a : ℕ → ℕ → ℕ)
    (ha : ∀ n m, a n m = a (n - 1) (m - 1) + 1) :
    a 9 5 = 1005 ∧
    a 2010 1000 = 2011 ∧
    {p | ∃ n m, p = a n m ∧ p = 1005 ∧ n ≤ 2010}.encard = 2011 := by

  have h0 := ha 0 0 
  simp at h0 
  all_goals omega