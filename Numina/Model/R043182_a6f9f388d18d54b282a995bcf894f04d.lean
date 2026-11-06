import Mathlib

theorem number_theory_19250 :
    IsLeast {b | (Nat.digits b 423).length = 3} 8 := by
  constructor
  · -- First verify that 8 is in the set
    show (Nat.digits 8 423).length = 3
    native_decide
  · -- Now verify that 8 is the smallest such base
    intro b hb
    have h1 : (Nat.digits b 423).length = 3 := hb
    by_contra h
    push_neg at h
    interval_cases b <;> norm_num at h1 <;> all_goals contradiction