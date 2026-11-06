import Mathlib

theorem number_theory_174180 :
    IsGreatest {n | ∃ k, n = k^2 ∧ (Nat.digits 10 n).length = 4 ∧
      (Nat.digits 10 n)[3]! + (Nat.digits 10 n)[1]! = 9 ∧
      (Nat.digits 10 n)[2]! + (Nat.digits 10 n)[0]! = 9} 9801 := by
  constructor
  · -- Show that 9801 is in the set, with k = 99
    use 99
    all_goals norm_num
  · -- Show that 9801 is the greatest element in the set
    intro n hn
    rcases hn with ⟨k, rfl, hk1, hk2, hk3⟩
    by_contra h
    push_neg at h
    have h1 : k ≥ 100 := by
      by_contra h1
      push_neg at h1
      have h2 : k ≤ 99 := by linarith
      have h3 : k ^ 2 ≤ 9801 := by
        nlinarith [show k ≤ 99 by linarith]
      linarith
    have h2 : k ^ 2 ≥ 10000 := by
      nlinarith
    have h3 : (Nat.digits 10 (k ^ 2)).length > 4 := by
      have h4 : k ^ 2 ≥ 10000 := by linarith
      have h5 : (Nat.digits 10 (k ^ 2)).length > 4 := by
        have h6 : (Nat.digits 10 (k ^ 2)).length = Nat.log 10 (k ^ 2) + 1 := by
          rw [Nat.digits_len]
          all_goals
            omega
        rw [h6]
        have h7 : Nat.log 10 (k ^ 2) ≥ 4 := by
          apply Nat.le_log_of_pow_le (by norm_num)
          all_goals
            omega
        omega
      linarith
    linarith