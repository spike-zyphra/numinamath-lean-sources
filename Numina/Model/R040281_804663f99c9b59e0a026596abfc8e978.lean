import Mathlib

theorem number_theory_19231 : IsGreatest {N | N^2 ∣ Nat.factorial 8} 24 := by
  constructor
  · -- Show 24 is in the set
    native_decide
  · -- Show there is no larger element in the set
    intro N hN
    have h1 : N ^ 2 ∣ Nat.factorial 8 := hN
    have h2 : N ≤ 24 := by
      by_contra h
      push_neg at h
      have h3 : N ^ 2 ∣ Nat.factorial 8 := h1
      have h4 : Nat.factorial 8 = 40320 := by
        norm_num [Nat.factorial]
      rw [h4] at h3
      have h5 : N ≤ 200 := by
        by_contra h'
        push_neg at h'
        have h6 : N ^ 2 > 40320 := by
          have h7 : N ≥ 201 := by omega
          have h8 : N ^ 2 ≥ 201 ^ 2 := by nlinarith
          nlinarith
        have h9 : N ^ 2 ∣ 40320 := h3
        have h10 : N ^ 2 ≤ 40320 := by
          exact Nat.le_of_dvd (by norm_num) h9
        linarith
      interval_cases N <;> norm_num at h3
      <;> all_goals
        omega
    linarith