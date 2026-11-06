import Mathlib

theorem number_theory_5616 :
    IsGreatest {n | n ∈ Finset.Icc 1000 9999 ∧ Nat.gcd n 1216 = 304} 9424 := by
  constructor
  · -- Show that 9424 is in the set
    constructor
    · -- Verify 9424 is in the range [1000, 9999]
      native_decide
    · -- Verify gcd(9424, 1216) = 304
      native_decide
  · -- Show that 9424 is the greatest element in the set
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1r⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [Nat.gcd] at hn2 ⊢ <;> all_goals omega