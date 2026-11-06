import Mathlib

/- a) Let $p$ be a prime number congruent to 3 modulo 4, and $a$ and $b$ be two integers such that $p \mid (a^2 + b^2)$. Show that $p \mid a$ and $p \mid b$.

b) Deduce that there are infinitely many prime numbers congruent to 1 modulo 4. -/
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
--Let us assume that the set S is finite.
  by_contra hfinite
  simp only [Set.not_infinite] at hfinite
--We will need to use that it is also a finite type.
  have fintype: Fintype S := by exact hfinite.fintype
--We construct the numner N given by the product of all the primes in S.
  set N := ∏ q in S , q with hN
--We construct the number M = a^2+b^2, where a=2N and b=1.
  set M := (2*N)^2+1^2 with hM
--We observe that primes dividing M must be congruent to 3 modulo 4, since all the others divide M-1.
  have hpdvdM: ∀ p : ℕ , (Nat.Prime p) ∧ p ∣ M → p % 4 = 3 := by
    intro p ⟨hp,hpdiv⟩
--We do a case distinction, eliminating all possible congruences of p modulo 4 different from 3.
    mod_cases hpmod4 : p % 4
    · rw [Nat.modEq_zero_iff_dvd, Nat.dvd_prime hp] at hpmod4
      cases hpmod4 with
      | inl => linarith
      | inr => have : Nat.Prime 4 := by
                rw [(by assumption : 4=p)]; exact hp
               contradiction
    · exfalso
      have : p ∈ S := by
        rw [hS, Set.mem_setOf]
        exact ⟨hp,hpmod4⟩
      have : p ∣ N := by
        rw [hN]
        apply Finset.dvd_prod_of_mem
        simp only [Set.mem_toFinset, this]
      have : p ∣ 1 := by
        rw [hM] at hpdiv
        ring_nf at hpdiv
        zify at hpdiv
        apply Int.dvd_iff_dvd_of_dvd_add at hpdiv
        rw_mod_cast [hpdiv, Nat.Prime.dvd_mul hp]
        left
        exact Dvd.dvd.pow this (by linarith : 2 ≠ 0)
      exact Nat.Prime.not_dvd_one hp this
    · exfalso
      have : Even 4 := by exact Nat.even_iff.mpr rfl
      have : p = 2 := by
        rw [← Nat.Prime.even_iff hp, ← Even.mod_even_iff this]
        rw [hpmod4]
        simp only [Nat.reduceMod, even_two]
      have : p ∣ 1 := by
        rw [hM] at hpdiv
        ring_nf at hpdiv
        zify at hpdiv
        apply Int.dvd_iff_dvd_of_dvd_add at hpdiv
        rw_mod_cast [hpdiv, Nat.Prime.dvd_mul hp]
        right
        rw [this]
        norm_num
      exact Nat.Prime.not_dvd_one hp this
    · assumption
--Since M is not 1, it is divisible by at least one prime p.
  have : ∃ p : ℕ , (Nat.Prime p) ∧ p ∣ M := by
    rw [← Nat.ne_one_iff_exists_prime_dvd]
    intro hM1
    rw [hM1] at hM
    ring_nf at hM
    rw [self_eq_add_right] at hM
    simp only [mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, or_false] at hM
    rw [hM] at hN
    symm at hN
    rw [Finset.prod_eq_zero_iff] at hN
    simp only [Set.mem_toFinset, exists_eq_right] at hN
    rw [hS, Set.mem_setOf] at hN
    omega
  obtain ⟨p, hp⟩ := this
  rw [hM] at hp
--By the above, this prime is 3 modulo 4.
  have pmod4 := hpdvdM p hp
--Using part a, we find a contradiction (namely that p should divide 1).
  have parta : p ∣ (2*N) ∧ p ∣ 1 := by
    apply_mod_cast number_theory_295834a p (2*N) 1 ⟨hp.1,pmod4,?_⟩
    exact_mod_cast hp.2
  exact Nat.Prime.not_dvd_one hp.1 parta.2