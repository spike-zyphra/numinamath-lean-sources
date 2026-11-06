import Mathlib

def is_interesting (A : ℕ) : Prop :=
  A % (A / 1000) = 0 ∧ A % (A / 100) = 0 ∧ A % (A / 10) = 0 ∧ A % A = 0

theorem number_theory_57285 :
    IsGreatest {A | is_interesting A ∧ (Nat.digits 10 A).length = 4 ∧ (Nat.digits 10 A).toFinset.card = 4} 3570 := by
  constructor
  · -- Show that 3570 is indeed in the set
    constructor
    · -- Show that 3570 is interesting
      unfold is_interesting
      native_decide
    constructor
    · -- Show that the length of digits in 3570 is 4
      native_decide
    · -- Show that the cardinality of the digits in 3570 is 4
      native_decide
  · -- Now, we need to prove that 3570 is the greatest such number
    intro A h
    rcases h with ⟨h_interesting, h_length, h_card⟩
    by_contra h'
    push_neg at h'
    have h1 : A > 3570 := by linarith
    have h2 : A < 10000 := by
      have h3 : (Nat.digits 10 A).length = 4 := h_length
      by_contra h4
      push_neg at h4
      have h5 : (Nat.digits 10 A).length > 4 := by
        have h6 : (Nat.digits 10 A).length = Nat.log 10 A + 1 := by
          rw [Nat.digits_len]
          all_goals omega
        have h7 : Nat.log 10 A + 1 > 4 := by
          have h8 : 10 ^ 4 ≤ A := by linarith
          have h9 : Nat.log 10 A ≥ 4 := by
            apply Nat.le_log_of_pow_le (by norm_num) h8
          omega
        linarith [h6, h7]
      omega
    -- Now we have 3570 < A < 10000, so we can check all these possibilities
    interval_cases A <;> norm_num [is_interesting] at h_interesting h_length h_card <;> all_goals contradiction