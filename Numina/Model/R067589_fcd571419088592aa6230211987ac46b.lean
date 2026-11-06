import Mathlib

theorem number_theory_19419 :
    IsGreatest {n | Odd n ∧ n ∣ Nat.factorial 5} 15 := by
  constructor
  · -- Show that 15 is in the set
    constructor
    · -- Show that 15 is odd
      exact Nat.odd_iff.mpr (by norm_num)
    · -- Show that 15 divides 5!
      native_decide
  · -- We need to show that for any n in the set, n ≤ 15
    intro n hn
    rcases hn with ⟨h_odd, h_div⟩
    have h1 : n ≤ Nat.factorial 5 := by
      exact Nat.le_of_dvd (by positivity) h_div
    have h2 : Nat.factorial 5 = 120 := rfl
    rw [h2] at h1 h_div
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at h_div h_odd h <;> all_goals contradiction