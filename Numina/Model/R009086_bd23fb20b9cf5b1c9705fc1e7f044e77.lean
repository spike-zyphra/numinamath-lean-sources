import Mathlib

theorem number_theory_12828 : IsLeast {b : ℕ | (Nat.digits b 62).length = 3} 4 := by 
  constructor
  · -- Show that 4 is indeed in the set
    show (Nat.digits 4 62).length = 3
    norm_num
  · -- Show that 4 is the smallest
    intro b hb
    have h : (Nat.digits b 62).length = 3 := hb
    by_contra h1
    push_neg at h1
    interval_cases b <;> norm_num at h <;> all_goals contradiction