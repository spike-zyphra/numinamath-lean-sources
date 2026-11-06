import Mathlib

theorem number_theory_157937 (p P : ℕ) (hp : Nat.Prime p) (hP : Nat.Prime P)
    (h : P = 14 * p^2 + 1) :
    (p, P) = (3, 127) := by
  have h1 : p ≥ 2 := Nat.Prime.two_le hp
  have h2 : P ≥ 2 := Nat.Prime.two_le hP
  by_cases hp3 : p ≤ 3
  · interval_cases p <;> norm_num [h] at hP ⊢ <;> tauto
  · -- p > 3
    have hp4 : p > 3 := by omega
    have hp1 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases hp1 with (h11 | h11 | h11)
    · -- p % 3 = 0
      have h3 : ¬Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega
      contradiction
    · -- p % 3 = 1
      have h4 : P % 3 = 0 := by
        simp [h, Nat.add_mod, Nat.mul_mod, h11, pow_two]
        all_goals omega
      have h5 : ¬Nat.Prime P := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ P by omega)
        all_goals
        nlinarith [show P > 3 from by nlinarith [show p > 2 by omega, sq_nonneg (p : ℕ), sq_pos_of_pos (show (p : ℕ) > 0 by omega) ] ]
      contradiction
    · -- p % 3 = 2
      have h4 : P % 3 = 0 := by
        simp [h, Nat.add_mod, Nat.mul_mod, h11, pow_two]
        all_goals omega
      have h5 : ¬Nat.Prime P := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ P by omega)
        all_goals
        nlinarith [show P > 3 from by nlinarith [show p > 2 by omega, sq_nonneg (p : ℕ), sq_pos_of_pos (show (p : ℕ) > 0 by omega) ] ]
      contradiction