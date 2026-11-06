import Mathlib

theorem number_theory_207846 (p d : ℕ) (hp : 0 < p) (hd : 0 < d) (hd' : ¬6 ∣ d)
    (h₀ : Nat.Prime p ∧ Nat.Prime (p + d) ∧ Nat.Prime (p + 2 * d)) :
    3 ∣ p + 3 * d := by
  by_cases h₁ : p = 2
  . have h₂ : 2 ∣ p + 2 * d := by
      simp [h₁]
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two h₀.2.2] at h₂
    omega
  . replace h₁ : p > 2 := by
      have := Nat.Prime.two_le h₀.1
      omega
    have h₂ : ¬2 ∣ p := by
      by_contra! h₂
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two h₀.1] at h₂
      omega
    have h₃ : ¬2 ∣ (p + d) := by
      by_contra! h₃
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two h₀.2.1] at h₃
      omega
    replace h₃ : 2 ∣ d := by
      omega
    have h₄ : ¬3 ∣ d := by
      by_contra! h₄
      absurd hd'
      rw [show 6 = 2 * 3 by norm_num]
      apply Nat.Prime.dvd_mul_of_dvd_ne (by norm_num) Nat.prime_two Nat.prime_three h₃ h₄
    have h₅ : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
      omega
    have h₆ : d % 3 = 1 ∨ d % 3 = 2 := by
      omega
    have h₇ : p % 3 = 0 ∨ (p + d) % 3 = 0 ∨ (p + 2 * d) % 3 = 0 := by
      omega
    by_cases h₈ : p = 3
    . omega
    . rcases h₇ with (h₇ | h₇ | h₇)
      . omega
      . rw [<-Nat.dvd_iff_mod_eq_zero] at h₇
        rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three h₀.2.1] at h₇
        omega
      . rw [<-Nat.dvd_iff_mod_eq_zero] at h₇
        rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three h₀.2.2] at h₇
        omega
