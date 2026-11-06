import Mathlib

open Finset

theorem number_theory_187443 {n : ℕ} (hn : n > 0) :
    (Nat.digits 4 n).length = 3 → ∑ i ∈ range (Nat.digits 4 n).length, (Nat.digits 4 n)[i]!^2 < n := by
  intro h
  have h1 : n ≥ 16 := by 
    by_contra h1
    push_neg at h1
    interval_cases n <;> norm_num at h <;> all_goals try { contradiction }
  have h2 : n < 64 := by
    by_contra h2
    push_neg at h2
    have h3 : (Nat.digits 4 n).length ≥ 4 := by
      have h4 : n ≥ 64 := by omega
      have h5 : (Nat.digits 4 n).length = Nat.log 4 n + 1 := by
        rw [Nat.digits_len]
        all_goals omega
      have h6 : Nat.log 4 n ≥ 3 := by
        have h7 : n ≥ 64 := by omega
        have h8 : 4 ^ 3 ≤ n := by omega
        have h9 : Nat.log 4 n ≥ 3 := by
          apply Nat.le_log_of_pow_le (by norm_num) h8
        linarith
      have h10 : (Nat.digits 4 n).length ≥ 3 + 1 := by 
        rw [h5]
        omega
      omega
    omega
  interval_cases n <;> norm_num [Finset.sum_range_succ, Nat.digits, Nat.digitsAux] <;> all_goals omega