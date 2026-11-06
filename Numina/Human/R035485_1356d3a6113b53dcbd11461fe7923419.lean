import Mathlib

/- Prove that there exist infinitely many even positive integers $k$ such that for every prime $p$ the number $p^{2}+k$ is composite. -/
theorem number_theory_241062 :
    ∀ n : ℕ, ∃ k > n, Even k ∧ ∀ p : ℕ, Nat.Prime p → ¬Nat.Prime (p ^ 2 + k) := by
  intro n
  let k:= 30 * n + 26
  use k
  simp [k]
  constructor
  . omega
  . constructor
    . have o: 30 * n + 26 = 2 * (15 * n + 13) := by ring
      rw [o]
      apply even_two_mul
    . intro p
      intro hp
      by_cases hp1: p = 3
      simp [hp1]
      have o: 9 + (30 * n + 26) = 5 * (6 * n + 7) := by ring
      rw [o]
      have i: 5 ∣ 5 * (6 * n + 7) := by
        apply dvd_mul_right
      apply Nat.not_prime_of_dvd_of_ne i
      . omega
      . linarith
      . have dvd: 3 ∣ p ^ 2 + (30 * n + 26) := by
          have dvd_trick: 3 ∣ (p - p % 3) := by
            have h : p = 3 * (p / 3) + p % 3 := by symm; apply Nat.div_add_mod p 3
            nth_rewrite 1 [h]
            omega
          have ineq: 2 ≤ p := by apply Nat.Prime.two_le hp
          have Prime_Mod_three : 3 ∣ p ^ 2 - 1  := by
            have j: p % 3 ≠ 0 := by
              by_contra! j
              replace j: 3 ∣ p := by apply Nat.dvd_of_mod_eq_zero j
              apply Nat.not_prime_of_dvd_of_ne j
              . omega
              . tauto
              . tauto
            by_cases q: p % 3 = 1
            . rw [q] at dvd_trick
              apply exists_eq_mul_right_of_dvd at dvd_trick
              obtain ⟨t, ht⟩ := dvd_trick
              replace ht: p = 3 * t + 1 := by rw [← ht]; symm; rw [Nat.sub_add_cancel]; nlinarith
              have eq: p ^ 2 - 1 = 3 * (t * (3 * t + 2)) := by
                simp [ht]
                ring_nf
                calc
                  1 + t * 6 + t ^ 2 * 9 - 1 = 1 + (t * 6 + t ^ 2 * 9) - 1 := by ring_nf
                                           _= t * 6 + t ^ 2 * 9 := by apply Nat.add_sub_cancel_left
              rw [eq]
              apply dvd_mul_right
            . replace q: p % 3 = 2 := by
                by_contra! q
                have o: p % 3 < 3 := by apply Nat.mod_lt p; omega
                omega
              rw [q] at dvd_trick
              apply exists_eq_mul_right_of_dvd at dvd_trick
              obtain ⟨t, ht⟩ := dvd_trick
              replace ht: p = 3 * t + 2 := by rw [← ht]; symm; rw [Nat.sub_add_cancel]; nlinarith
              have eq: p ^ 2 - 1 = 3 * (3 * t ^ 2 + 4 * t + 1) := by
                simp [ht]
                ring_nf
                calc
                  4 + t * 12 + t ^ 2 * 9 - 1 = 4 + (t * 12 + t ^ 2 * 9) - 1 := by ring_nf
                                           _= 4 - 1 + (t * 12 + t ^ 2 * 9) := by apply Nat.sub_add_comm; omega
                                            _= 3 + t * 12 + t ^ 2 * 9 := by ring_nf
              rw [eq]
              apply dvd_mul_right
          apply exists_eq_mul_right_of_dvd at Prime_Mod_three
          obtain ⟨t, ht⟩ := Prime_Mod_three
          replace ht: p ^ 2 = 3 * t + 1 := by rw [← ht]; symm; rw [Nat.sub_add_cancel]; nlinarith
          have eq: p ^ 2 + (30 * n + 26) = 3 * (t + 10 * n + 9) := by simp [ht];ring
          rw [eq]
          apply dvd_mul_right
        apply Nat.not_prime_of_dvd_of_ne dvd
        . omega
        . nlinarith