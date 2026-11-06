import Mathlib

theorem number_theory_188865 (p : ℕ) (hp : Nat.Prime p) (hpn2 : p ≠ 2) (hpn3 : p ≠ 3) :
    p^2 ≡ 1 [MOD 12] := by
  have h1 : p ≥ 2 := Nat.Prime.two_le hp
  have h2 : p ≠ 2 := hpn2
  have h3 : p ≠ 3 := hpn3
  have h4 : p ≥ 5 := by
    by_contra h
    push_neg at h
    have : p < 5 := by linarith
    interval_cases p <;> norm_num at hp h1 h2 h3 <;> all_goals contradiction
  have h5 : p % 2 ≠ 0 := by
    by_contra h
    have h6 : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
    contradiction
  have h6 : p % 3 ≠ 0 := by
    by_contra h
    have h7 : 3 ∣ p := by omega
    have h8 : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
    contradiction
  have h8 : p % 3 = 1 ∨ p % 3 = 2 := by
    omega
  have h9 : p^2 % 3 = 1 := by
    rcases h8 with (h8 | h8)
    · simp [Nat.pow_mod, h8]
    · simp [Nat.pow_mod, h8]
  have h10 : p^2 % 4 = 1 := by
    have h8 : p % 2 = 1 := by omega
    have h12 : p % 4 = 1 ∨ p % 4 = 3 := by
      omega
    rcases h12 with (h | h)
    · simp [Nat.pow_mod, h]
    · simp [Nat.pow_mod, h]
  have h13 : p^2 % 12 = 1 := by
    omega
  show p^2 ≡ 1 [MOD 12]
  exact h13