import Mathlib

theorem number_theory_5189 (p : ℕ) (hp : Nat.Prime p) (h : 3 < p) :
    ∃ k : ℕ, p = 6 * k + 1 ∨ p = 6 * k + 5 := by
  have h1 : p % 6 = 1 ∨ p % 6 = 5 := by
    by_contra h2
    push_neg at h2
    have h2 : p % 6 = 0 ∨ p % 6 = 2 ∨ p % 6 = 3 ∨ p % 6 = 4 := by 
      omega
    rcases h2 with (h2 | h2 | h2 | h2)
    · -- From p % 6 = 0, we have that 2 divides p
      have h3 : p % 2 = 0 := by
        omega
      have h4 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals omega
      contradiction
    · -- From p % 6 = 2, we have that 2 divides p
      have h3 : p % 2 = 0 := by 
        omega
      have h4 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals omega
      contradiction
    · -- From p % 6 = 3, we have that 3 divides p
      have h3 : p % 3 = 0 := by 
        omega
      have h4 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega
      contradiction
    · -- From p % 6 = 4, we have that 2 divides p
      have h3 : p % 2 = 0 := by 
        omega
      have h4 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals omega
      contradiction
  rcases h1 with (h1 | h1)
  · -- Case where p % 6 = 1
    use (p - 1) / 6
    left
    omega
  · -- Case where p % 6 = 5
    use (p - 5) / 6
    right
    omega