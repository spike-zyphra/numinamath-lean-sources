import Mathlib

theorem number_theory_295834a : ∀ (p : ℕ) (a b : ℤ) , (Nat.Prime p ∧ p % 4 = 3 ∧ (p : ℤ) ∣ a^2 + b^2) → ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b):= by
--Let p be a prime that is 3 mod 4 and that divides a^2+b^2.
  intro p a b h
  rcases h with ⟨hp,h2⟩
--We will need to use that p is a prime as a Fact, and that the integer number p is prime.
  have hpFact: Fact (Nat.Prime p) := ⟨hp⟩
  have hpZ : (Prime (p : ℤ)) := by exact Nat.prime_iff_prime_int.mp hp
  rcases h2 with ⟨hpmod4,hpdiv⟩
--From our hypothesis, it is equivalent to show that p divides either of a and b.
  have pdiva_iff_pdivb: (p : ℤ) ∣ a ↔ (p : ℤ) ∣ b := by
    constructor
    · intro ha
      have h1 : (p : ℤ) ∣ a^2 := by exact dvd_pow ha (by norm_num : 2 ≠ 0)
      have h2 : (p : ℤ) ∣ b^2 := by exact (Int.dvd_iff_dvd_of_dvd_add hpdiv).mp h1
      exact Prime.dvd_of_dvd_pow hpZ h2
    · intro hb
      have h1 : (p : ℤ) ∣ b^2 := by exact dvd_pow hb (by norm_num : 2 ≠ 0)
      have h2 : (p : ℤ) ∣ a^2 := by rw [add_comm] at hpdiv; exact (Int.dvd_iff_dvd_of_dvd_add hpdiv).mp h1
      exact Prime.dvd_of_dvd_pow hpZ h2
--We will then show that p divides b.
  suffices (p : ℤ) ∣ b by
    simp only [this, and_true, pdiva_iff_pdivb]
--The hypothesis p | a^2+b^2 is equivalent to having a^2 congruent to -b^2 modulo p.
  have : (a^2 : ZMod p) = (-b^2 : ZMod p) := by
    rw [← add_eq_zero_iff_eq_neg]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hpdiv
    exact_mod_cast hpdiv
--We conclude by contradiction, using that from the above, -1 should be a square modulo p, but since p is 3 mod 4 this is impossible
  by_contra hpb
  apply ZMod.mod_four_ne_three_of_sq_eq_neg_sq' at this
  · contradiction
  · intro bzero
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at bzero
    contradiction

theorem number_theory_295834b (hS : S = {p : ℕ | Nat.Prime p ∧ p % 4 = 1}) : (S.Infinite) := by
  rw [hS]
  apply Nat.infinite_setOf_prime_modEq_one
  all_goals norm_num