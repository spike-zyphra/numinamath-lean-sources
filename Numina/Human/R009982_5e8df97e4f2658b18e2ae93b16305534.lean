import Mathlib

theorem number_theory_183991 (p : ℕ) (hp : Nat.Prime p) (h : 3 < p) :
    (p ^ 2) % 12 = 1 := by
  have H : p % 6 = 1 ∨ p % 6 = 5 := by
    mod_cases H : p % 6
    . apply Nat.dvd_of_mod_eq_zero at H
      have hp2 : 2 ∣ p := Nat.dvd_trans (by norm_num) H
      rw [Nat.prime_dvd_prime_iff_eq (by norm_num) hp] at hp2
      simp [← hp2] at h
    . exact Or.inl H
    . have hp2 : 2 ∣ p := by
        use (p / 6) * 3 + 1
        have k := Nat.div_add_mod p 6
        rw [H] at k
        linear_combination -k
      rw [Nat.prime_dvd_prime_iff_eq (by norm_num) hp] at hp2
      simp [← hp2] at h
    . have hp3 : 3 ∣ p := by
        use (p / 6) * 2 + 1
        have k := Nat.div_add_mod p 6
        rw [H] at k
        linear_combination -k
      rw [Nat.prime_dvd_prime_iff_eq (by norm_num) hp] at hp3
      simp [← hp3] at h
    . have hp2 : 2 ∣ p := by
        use (p / 6) * 3 + 2
        have k := Nat.div_add_mod p 6
        rw [H] at k
        linear_combination -k
      rw [Nat.prime_dvd_prime_iff_eq (by norm_num) hp] at hp2
      simp [← hp2] at h
    . exact Or.inr H
  rcases H with H | H
  . have k := Nat.div_add_mod p 6
    rw [H] at k
    rw [← k]
    ring_nf
    omega
  . have k := Nat.div_add_mod p 6
    rw [H] at k
    rw [← k]
    ring_nf
    omega
