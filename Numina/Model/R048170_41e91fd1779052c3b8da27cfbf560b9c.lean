import Mathlib

theorem number_theory_15780 :
    IsGreatest {n > 0 | ∃(A B C : ℕ), A < 7 ∧ B < 7 ∧ C < 7 ∧ Nat.digits 7 n = [C, B, A] ∧ Nat.digits 11 n = [A, B, C]} 247 := by
  constructor
  · -- Show 247 is in the set
    constructor
    · norm_num
    · -- Show existence of A, B, C
      use 5, 0, 2
      simp
      all_goals native_decide
  · -- Show that 247 is the greatest
    intro n hn
    rcases hn with ⟨hn_pos, A, B, C, hA, hB, hC, h7, h11⟩
    have h1 : n = 49 * A + 7 * B + C := by
      rw [← Nat.ofDigits_digits 7 n]
      rw [h7]
      simp [Nat.ofDigits, mul_add, mul_one]
      all_goals omega
    have h2 : n = 121 * C + 11 * B + A := by
      rw [← Nat.ofDigits_digits 11 n]
      rw [h11]
      simp [Nat.ofDigits, mul_add, mul_one]
      all_goals omega
    have h_eq1 : 49 * A + 7 * B + C = 121 * C + 11 * B + A := by
      linarith [h1, h2]
    interval_cases A <;> interval_cases B <;> interval_cases C <;> omega