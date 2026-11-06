import Mathlib

theorem number_theory_111876 (a : ℕ) :
    (Nat.digits 10 a).length = 1 ∧ 6 ∣ Nat.ofDigits 10 [a, 5, 7, 8] ↔ a = 4 := by
  constructor
  · -- Assume (Nat.digits 10 a).length = 1 ∧ 6 ∣ Nat.ofDigits 10 [a, 5, 7, 8], prove a = 4
    rintro ⟨ha1, ha2⟩
    have h1 : a < 10 := by
      by_contra h
      push_neg at h
      have h2 : (Nat.digits 10 a).length > 1 := by
        have h3 : a > 9 := by linarith
        have h4 : (Nat.digits 10 a).length = Nat.log 10 a + 1 := by
          rw [Nat.digits_len]
          all_goals linarith
        have h5 : Nat.log 10 a ≥ 1 := by
          have h6 : 10 ^ 1 ≤ a := by linarith
          exact Nat.le_log_of_pow_le (by norm_num) h6
        have h7 : (Nat.digits 10 a).length ≥ 2 := by
          rw [h4]
          omega
        omega
      omega
    interval_cases a <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at ha1 ha2 ⊢
    <;> omega
  · -- Assume a = 4, prove (Nat.digits 10 a).length = 1 ∧ 6 ∣ Nat.ofDigits 10 [a, 5, 7, 8]
    intro h
    rw [h]
    constructor
    · -- Show length of digits is 1
      norm_num [Nat.digits, Nat.digitsAux]
    · -- Show 6 divides the number
      norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]