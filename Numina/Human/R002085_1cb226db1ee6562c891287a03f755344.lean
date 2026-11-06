import Mathlib

def is_interesting (n : ℕ) := ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p * q

lemma four_dvd_interesting {n : ℕ} (hn : is_interesting n) (h : 4 ∣ n): n = 4 := by
  rcases hn with ⟨p, q, hp, hq, hn_eq⟩
  by_cases hp2 : p % 2 = 1
  · -- p is odd
    have h1 : q % 2 = 0 := by
      have h2 : (p * q) % 2 = 0 := by
        omega
      have h3 : p % 2 = 1 := hp2
      have h4 : q % 2 = 0 := by
        simp [Nat.mul_mod, h3] at h2
        omega
      assumption
    have hq2 : q = 2 := by
      by_cases hq2 : q > 2
      · -- If q > 2, it's an even number greater than 2, so it's not prime - contradiction
        have hq2' : ¬ Nat.Prime q := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
          all_goals omega
        contradiction
      · -- q ≤ 2
        interval_cases q <;> try { tauto }
    rw [hq2] at hn_eq
    have h2 : p % 2 = 1 := hp2
    have h3 : p % 2 = 0 := by
      omega
    omega
  · -- p is even
    have hp2 : p = 2 := by
      by_cases hp2 : p > 2
      · -- If p > 2, it's an even number greater than 2, so it's not prime - contradiction
        have hp2' : ¬ Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals omega
        contradiction
      · -- p ≤ 2
        interval_cases p <;> try { tauto }
    rw [hp2] at hn_eq
    have h1 : q % 2 = 0 := by
      have h2 : (2 * q) % 2 = 0 := by
        omega
      have h3 : q % 2 = 0 := by
        omega
      assumption
    have hq2 : q = 2 := by
      by_cases hq2 : q > 2
      · -- If q > 2, it's an even number greater than 2, so it's not prime - contradiction
        have hq2' : ¬ Nat.Prime q := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
          all_goals omega
        contradiction
      · -- q ≤ 2
        interval_cases q <;> try { tauto }
    rw [hq2] at hn_eq
    nlinarith


/- Let’s call a positive integer [i]interesting[/i] if it is a product of two (distinct or equal) prime numbers. What is the greatest number of consecutive positive integers all of which are interesting? -/
theorem number_theory_63188 :
    IsGreatest {k | ∃ m, ∀ i ∈ Finset.range k, is_interesting (m + i)} 3 := by


  constructor
  . simp
    use 33
    intro i hi
    unfold is_interesting
    interval_cases i
    . use 3, 11
      decide
    . use 2, 17
      decide
    . use 5, 7
      decide
  . simp [upperBounds]
    intro k m hm
    by_contra hk
    simp at hk

    have h1: ∃ j, j < k ∧ 4 ∣ (m + j) := by
      mod_cases m % 4
      . use 0
        refine ⟨by omega, ?_⟩
        simp [Nat.ModEq] at H
        omega
      . use 3
        refine ⟨by omega, ?_⟩
        simp [Nat.ModEq] at H
        omega
      . use 2
        refine ⟨by omega, ?_⟩
        simp [Nat.ModEq] at H
        omega
      . use 1
        refine ⟨by omega, ?_⟩
        simp [Nat.ModEq] at H
        omega

    obtain ⟨j, hj1, hj2⟩ := h1

    have h2 := hm j hj1
    have h3 := four_dvd_interesting h2 hj2
    have h4 : m ≤ 4 := by omega

    have three_not_interesting: ¬ is_interesting 3 := by
      unfold is_interesting
      simp
      intro p hp q hq hpq
      have : Nat.Prime 3 := by decide
      rw [hpq] at this
      rw [Nat.prime_mul_iff] at this
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      . rw [h2] at hq
        contrapose hq
        decide
      . rw [h2] at hp
        contrapose hp
        decide

    have five_not_interesting: ¬ is_interesting 5 := by
      unfold is_interesting
      simp
      intro p hp q hq hpq
      have : Nat.Prime 5 := by decide
      rw [hpq] at this
      rw [Nat.prime_mul_iff] at this
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      . rw [h2] at hq
        contrapose hq
        decide
      . rw [h2] at hp
        contrapose hp
        decide

    interval_cases m
    . have := hm 3 (by omega)
      simp at this
      contradiction
    . have := hm 2 (by omega)
      simp at this
      contradiction
    . have := hm 1 (by omega)
      simp at this
      contradiction
    . have := hm 0 (by omega)
      simp at this
      contradiction
    . have := hm 1 (by omega)
      simp at this
      contradiction

