import Mathlib

theorem number_theory_13821 :
    IsGreatest {n | (Nat.digits 10 n).length = 3 ∧ n % ((Nat.digits 10 n).prod) = 0} 816 := by
  constructor
  · -- Show that 816 is in the set
    constructor
    · -- Show that 816 has 3 digits
      norm_num
    · -- Show that 816 is divisible by the product of its digits
      norm_num
  · -- Show that no number greater than 816 is in the set
    intro n hn
    rcases hn with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : n ≤ 999 := by
      by_contra h'
      push_neg at h'
      have h4 : (Nat.digits 10 n).length > 3 := by
        have h5 : Nat.log 10 n ≥ 3 := by 
          apply Nat.le_log_of_pow_le (by omega)
          omega
        have h6 : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by 
          rw [Nat.digits_len]
          all_goals omega
          all_goals try { tauto }
        omega
      omega
    interval_cases n <;> norm_num at h1 h2 h ⊢ 
      <;> all_goals try { contradiction }
      <;> try { tauto }