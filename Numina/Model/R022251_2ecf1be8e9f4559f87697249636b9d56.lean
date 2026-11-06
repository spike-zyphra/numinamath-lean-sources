import Mathlib

theorem number_theory_305420 (p : ℕ) (hp : p.Prime) (h : 3 < p) :
    p^2 ≡ 1 [MOD 24] := by
  have h1 : p % 2 = 1 := by
    by_contra h2
    have h3 : p % 2 = 0 := by omega
    have h4 : 2 ∣ p := by
      omega
    have h5 : ¬p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
      all_goals linarith
    contradiction

  have h2 : p % 3 ≠ 0 := by
    by_contra h3
    have h4 : 3 ∣ p := by 
      omega
    have h5 : ¬p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
      all_goals linarith
    contradiction

  have h11 : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨ p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23 := by
    omega

  rcases h11 with (h11 | h11 | h11 | h11 | h11 | h11 | h11 | h11)
  · -- p ≡ 1 [MOD 24]
    simp [Nat.ModEq, Nat.pow_mod, h11]
    all_goals omega
  · -- p ≡ 5 [MOD 24]
    simp [Nat.ModEq, Nat.pow_mod, h11]
    all_goals omega
  · -- p ≡ 7 [MOD 24]
    simp [Nat.ModEq, Nat.pow_mod, h11]
    all_goals omega
  · -- p ≡ 11 [MOD 24]
    simp [Nat.ModEq, Nat.pow_mod, h11]
    all_goals omega
  · -- p ≡ 13 [MOD 24]
    simp [Nat.ModEq, Nat.pow_mod, h11]
    all_goals omega
  · -- p ≡ 17 [MOD 24]
    simp [Nat.ModEq, Nat.pow_mod, h11]
    all_goals omega
  · -- p ≡ 19 [MOD 24]
    simp [Nat.ModEq, Nat.pow_mod, h11]
    all_goals omega
  · -- p ≡ 23 [MOD 24]
    simp [Nat.ModEq, Nat.pow_mod, h11]
    all_goals omega