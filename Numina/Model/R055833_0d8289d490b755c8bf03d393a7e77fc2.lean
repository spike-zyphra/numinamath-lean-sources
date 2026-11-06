import Mathlib

theorem number_theory_242715 (p : ℕ) (hp : p.Prime) (h : (p^2 + 8).Prime) :
    (p^3 + 4).Prime := by
  have h2 : p ≥ 2 := Nat.Prime.two_le hp
  by_cases h4 : p ≤ 3
  · interval_cases p <;> norm_num at hp h ⊢ <;> tauto
  · 
    have h5 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases h5 with (h5 | h5 | h5)
    · -- Case p ≡ 0 (mod 3): Then p is divisible by 3. Since p is prime and greater than 3, contradiction.
      have h6 : p % 3 = 0 := h5
      have h7 : ¬ p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega
      contradiction
    · -- Case p ≡ 1 (mod 3): Then p^2 ≡ 1 (mod 3), so p^2 + 8 ≡ 1 + 8 ≡ 9 ≡ 0 (mod 3). Therefore 3 divides p^2 + 8, which is prime, so contradiction since p > 3.
      have h8 : p % 3 = 1 := h5
      have h9 : (p ^ 2 + 8) % 3 = 0 := by
        simp [Nat.pow_mod, Nat.add_mod, h8]
        all_goals omega
      have h10 : ¬ (p^2 + 8).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p^2 + 8) by omega)
        all_goals
        have h4 : p ≥ 4 := by omega
        nlinarith [show p ≥ 4 by omega]
      contradiction
    · -- Case p ≡ 2 (mod 3): Then p^2 ≡ 4 ≡ 1 (mod 3), so p^2 + 8 ≡ 1 + 8 ≡ 9 ≡ 0 (mod 3). Therefore 3 divides p^2 + 8, which is prime, so contradiction since p > 3.
      have h11 : p % 3 = 2 := h5
      have h12 : (p ^ 2 + 8) % 3 = 0 := by
        simp [Nat.pow_mod, Nat.add_mod, h11]
        all_goals omega
      have h13 : ¬ (p^2 + 8).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p^2 + 8) by omega)
        all_goals
        have h4 : p ≥ 4 := by omega
        nlinarith [show p ≥ 4 by omega]
      contradiction