import Mathlib

theorem number_theory_40505 : IsGreatest {x | 17 % x = 30 % x} 13 := by
  constructor
  · -- Show $13 \in S$, which means $17 \bmod 13 = 30 \bmod 13$.
    norm_num
  · -- Show that if $x \in S$, then $x \leq 13$.
    intro x h_eq
    by_contra h
    push_neg at h
    -- Assume x > 13, so x ≥ 14.
    have h1 : x ≥ 14 := by omega
    have h3 : x ≤ 30 := by
      by_contra h4
      push_neg at h4
      have h4' : x > 30 := by linarith
      have h5 : 17 % x = 17 := by
        rw [Nat.mod_eq_of_lt]
        all_goals linarith
      have h6 : 30 % x = 30 := by 
        rw [Nat.mod_eq_of_lt]
        all_goals linarith
      have h7 : 17 % x = 30 % x := h_eq
      rw [h5, h6] at h7
      all_goals omega
    interval_cases x <;> norm_num at h_eq ⊢ <;> omega