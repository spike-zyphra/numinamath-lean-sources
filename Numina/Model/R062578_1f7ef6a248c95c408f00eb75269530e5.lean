import Mathlib

theorem number_theory_101682 (p : ℕ) (hp : Nat.Prime p) (h : 5 ≤ p) :
    24 ∣ (p^2 - 1) := by
  have h1 : p % 2 ≠ 0 := by
    by_contra h2
    have h4 : p % 2 = 0 := by
      omega
    have h5 : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
    contradiction
  have h2 : p % 3 ≠ 0 := by
    by_contra h3
    have h4 : p % 3 = 0 := by
      omega
    have h5 : 3 ∣ p := by
      omega
    have h6 : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
    contradiction
  have h3 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    omega
  have h4 : (p ^ 2) % 8 = 1 := by
    rcases h3 with (h | h | h | h)
    all_goals
      simp [pow_two, Nat.mul_mod, h]
  have h5 : (p ^ 2) % 3 = 1 := by
    have h6 : p % 3 = 1 ∨ p % 3 = 2 := by
      omega
    rcases h6 with (h6 | h6)
    all_goals
      simp [pow_two, Nat.mul_mod, h6]
  -- From divisibility by 8 and 3, we get divisibility by 24
  have h6 : (p ^ 2 - 1) % 8 = 0 := by
    omega
  have h7 : (p ^ 2 - 1) % 3 = 0 := by
    omega
  omega