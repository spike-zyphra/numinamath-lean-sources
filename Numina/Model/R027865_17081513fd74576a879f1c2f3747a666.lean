import Mathlib

theorem number_theory_182134 :
    IsGreatest {n | Even n ∧ (Nat.digits 10 n).length = 3 ∧ (Nat.digits 10 n).prod = 24 ∧ (Nat.digits 10 n).toFinset.card = 3} 614 := by
  constructor
  · -- Show 614 is in the set.
    constructor
    · -- Show 614 is even.
      exact ⟨307, by norm_num⟩
    constructor
    · -- Show (Nat.digits 10 614).length = 3
      native_decide
    constructor
    · -- Show (Nat.digits 10 614).prod = 24
      native_decide
    · -- Show (Nat.digits 10 614).toFinset.card = 3
      native_decide
  · -- Show that if n is in the set, then n ≤ 614
    intro n hn
    rcases hn with ⟨h1, h2, h3, h4⟩
    by_contra h
    push_neg at h
    have h5 : n > 614 := h
    have h6 : n < 1000 := by
      by_contra h
      push_neg at h
      have h6 : (Nat.digits 10 n).length > 3 := by
        have h7 : (Nat.log 10 n) ≥ 3 := by
          have h8 : n ≥ 1000 := by linarith
          have h9 : Nat.log 10 n ≥ 3 := by
            apply Nat.le_log_of_pow_le (by linarith) h8
          linarith
        have h8 : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by
          rw [Nat.digits_len]
          all_goals linarith
        linarith
      linarith
    interval_cases n <;> norm_num [Nat.even_iff] at h1 h3 h4 ⊢
    <;> tauto