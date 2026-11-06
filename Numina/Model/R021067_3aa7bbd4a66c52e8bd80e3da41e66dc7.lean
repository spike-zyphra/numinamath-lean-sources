import Mathlib

theorem number_theory_22856 (n : ℕ) :
    (Nat.digits 10 n).length = 1 ∧ 18 ∣ (Nat.ofDigits 10 [n, 4, 7, 3]) ↔ n = 4 := by
  constructor
  · -- Assume (Nat.digits 10 n).length = 1 ∧ 18 ∣ (Nat.ofDigits 10 [n, 4, 7, 3]), prove n = 4
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : n < 10 := by
      by_contra h4
      push_neg at h4
      have h4' : (Nat.digits 10 n).length > 1 := by
        have h5 : Nat.log 10 n ≥ 1 := by
          have : n ≥ 10 := by linarith
          have h6 : Nat.log 10 n ≥ 1 := by
            apply Nat.le_log_of_pow_le (by linarith) this
          linarith
        have : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by
          rw [Nat.digits_len]
          all_goals omega
        omega
      omega
    interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h1 h2 ⊢ <;> omega
  · -- Assume n = 4, prove (Nat.digits 10 n).length = 1 ∧ 18 ∣ (Nat.ofDigits 10 [n, 4, 7, 3])
    intro h
    rw [h]
    constructor
    · -- Check that the length of the digits of 4 is 1
      norm_num
    · -- Check that 18 divides 3744
      norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]