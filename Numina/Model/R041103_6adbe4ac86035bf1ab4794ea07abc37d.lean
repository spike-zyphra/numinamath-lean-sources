import Mathlib

theorem number_theory_244757 {A : ℕ} (hA : Nat.Prime A) (hA1 : Nat.Prime (A - 4)) (hA2 : Nat.Prime (A - 6))
    (hA3 : Nat.Prime (A - 12)) (hA4 : Nat.Prime (A - 18)) :
    A = 23 := by
  by_cases h1 : A > 23
  · -- Assume A > 23. Let's show a contradiction.
    have h2 : A % 5 = 0 ∨ A % 5 = 1 ∨ A % 5 = 2 ∨ A % 5 = 3 ∨ A % 5 = 4 := by
      omega
    rcases h2 with (h | h | h | h | h)
    · -- A % 5 = 0
      have h3 : ¬ Nat.Prime A := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ A by omega)
        all_goals omega
      contradiction
    · -- A % 5 = 1
      have h4 : (A - 6) % 5 = 0 := by
        omega
      have h5 : ¬ Nat.Prime (A - 6) := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (A - 6) by omega)
        all_goals omega
      contradiction
    · -- A % 5 = 2
      have h4 : (A - 12) % 5 = 0 := by
        omega
      have h5 : ¬ Nat.Prime (A - 12) := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (A - 12) by omega)
        all_goals omega
      contradiction
    · -- A % 5 = 3
      have h4 : (A - 18) % 5 = 0 := by
        omega
      have h5 : ¬ Nat.Prime (A - 18) := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (A - 18) by omega)
        all_goals omega
      contradiction
    · -- A % 5 = 4
      have h4 : (A - 4) % 5 = 0 := by
        omega
      have h5 : ¬ Nat.Prime (A - 4) := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (A - 4) by omega)
        all_goals omega
      contradiction
  · -- Assume A ≤ 23
    interval_cases A <;> norm_num at hA hA1 hA2 hA3 hA4 ⊢