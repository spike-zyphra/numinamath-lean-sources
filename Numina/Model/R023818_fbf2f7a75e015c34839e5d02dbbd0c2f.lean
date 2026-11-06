import Mathlib

theorem algebra_117069 (a : ℕ → ℤ) (ha : ∀ n, a n = a (n - 1) + 4) (ha0 : a 0 = 3) :
    a 3 = 7 ∧ a 4 = 11 ∧ a 5 = 15 ∧ a 6 = 19 ∧
    a 2013 = 8114406 ∧ ¬ ∃ n, a 2013 = n ^ 2 ∧
    ∑ i in Finset.range 2014, a i = 8114406 := by 
  -- Base contradiction from the inconsistent premises 
  have h0 := ha 0
  simp at h0
  -- Use linarith to derive a contradiction from ha0 and h0
  all_goals linarith [ha0, h0]