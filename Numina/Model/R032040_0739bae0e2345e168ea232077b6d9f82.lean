import Mathlib

theorem algebra_11428 {l1 l2 : ℕ} (hl1 : l1 = 38) (hl2 : l2 = 2 * l1) :
    l2 = 76 := by
  subst hl1 -- Substitute l1 with 38
  norm_num at hl2 ⊢ -- Calculate 2 * 38 to get 76 in the hypothesis
  exact hl2 -- The goal is now l2 = 76 and the hypothesis hl2 is l2 = 76