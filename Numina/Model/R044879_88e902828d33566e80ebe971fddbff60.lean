import Mathlib

theorem number_theory_15119 : IsGreatest {n : ℕ | 0 < n ∧ (Nat.digits 8 n).length = 3 ∧ 5 ∣ n} (Nat.ofDigits 8 [6, 7, 7]) := by
  constructor
  · -- Show that $776_8$ is in the set
    constructor
    · -- Show that 776_8 is positive
      norm_num [Nat.ofDigits]
    constructor
    · -- Show that the length of 776_8 in base 8 is 3
      norm_num [Nat.ofDigits]
    · -- Show that 5 divides 776_8
      norm_num [Nat.ofDigits]
  · -- Show that 776_8 is greatest in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_len, hn_div⟩
    have h1 : n < 512 := by
      by_contra h
      push_neg at h
      have h2 : (Nat.digits 8 n).length > 3 := by
        have h3 : Nat.log 8 n ≥ 3 := by
          have h4 : 8 ^ 3 ≤ n := by
            linarith
          exact Nat.le_log_of_pow_le (by norm_num) h4
        have h5 : (Nat.digits 8 n).length = Nat.log 8 n + 1 := by
          rw [Nat.digits_len]
          all_goals
            omega
        omega
      omega
    have h4 : n ≤ 511 := by
      omega
    have h5 : n ≤ 510 := by
      omega
    have h7 : Nat.ofDigits 8 [6, 7, 7] = 510 := by
      norm_num [Nat.ofDigits]
    have h8 : n ≤ 510 := h5
    have h9 : n ≤ Nat.ofDigits 8 [6, 7, 7] := by
      linarith [h7, h5]
    linarith