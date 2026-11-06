import Mathlib

open Finset

/-Let $n$ be a positive integer such that the sum of all the positive divisors of $n$ (except $n$ ) plus the number of these divisors is equal to $n$. Prove that $n=2 m^{2}$ for some integer $m$.-/
theorem number_theory_605764 (npos : 0 < n)
    (hn : ∑ d ∈ n.divisors, d - n + (n.divisors.card - 1) = n)
    : ∃ m, n = 2 * m ^ 2 := by
-- Prove that for any positive integer $m$, its number of divisors is odd if and only if all the powers occur in the prime factorization of $m$ is even
  have aux : ∀ m > 0, m.divisors.card % 2 = 1 ↔ ∀ p ∈ m.primeFactors,
  m.factorization p % 2 = 0 := by
    intro m mpos; constructor
    · intro h p hp; rw [Nat.card_divisors] at h
      rw [prod_nat_mod] at h; have : m.factorization p % 2 < 2 := by
        apply Nat.mod_lt; simp
      interval_cases h' : m.factorization p % 2; rfl
      rw [prod_eq_prod_diff_singleton_mul hp] at h
      rw [Nat.add_mod, h'] at h; simp at h; positivity
    contrapose!; intro h; have : #m.divisors % 2 < 2 := by
      apply Nat.mod_lt; simp
    interval_cases h' : #m.divisors % 2
    · rw [Nat.card_divisors, ← Nat.dvd_iff_mod_eq_zero] at h'
      rw [Prime.dvd_finset_prod_iff] at h'
      rcases h' with ⟨p, ⟨hp, hdvd⟩⟩; use p
      constructor; exact hp
      any_goals omega
      exact Nat.prime_two.prime
    contradiction
-- Prove that the number of divisors of $n$ is greater or equal to $1$
  have dcardpos : 1 ≤ n.divisors.card := by
    by_contra!; simp at this
    linarith only [this, npos]
-- Prove that $n$ is less or equal to the sum of divivors of $n$
  have lesumd: n ≤ ∑ d ∈ n.divisors, d := by
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
    apply Nat.le_add_left
-- Rearrange the terms in `hn` and modulo its both sides by $2$
  rw [← Nat.add_sub_assoc dcardpos] at hn
  rw [Nat.sub_eq_iff_eq_add, add_comm] at hn
  rw [← Nat.add_sub_assoc lesumd] at hn
  rw [Nat.sub_eq_iff_eq_add, show n+1+n = 2*n+1 by ring] at hn
  let mod2 := hn; apply_fun fun t => t % 2 at mod2
-- Split the goal to the cases when the number of divisors of $n$ is even or odd
  rw [Nat.add_mod] at mod2; have : #n.divisors % 2 < 2 := by
      apply Nat.mod_lt; simp
  interval_cases h : #n.divisors % 2
  · simp at mod2; rw [Nat.sum_divisors] at mod2
    replace mod2 : ∀ p ∈ n.primeFactors,
    (∑ k ∈ range (n.factorization p + 1), p ^ k) % 2 = 1 := by
      by_contra!; rcases this with ⟨p, ⟨hp, pmod2⟩⟩
      replace pmod2 : (∑ k ∈ range (n.factorization p + 1), p ^ k) % 2 = 0 := by omega
      rw [prod_eq_prod_diff_singleton_mul hp] at mod2
      rw [Nat.mul_mod, pmod2] at mod2
      simp [Nat.mul_add_mod] at mod2
  -- In the even case, prove that the powers of odd prime factors of $n$ is even
    replace mod2 : ∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p % 2 = 0 := by
      intro p hp pne; specialize mod2 p hp
      simp at hp; rcases hp with ⟨ppr, pdvd, _⟩
      have := ppr.two_le; replace pne : Odd p := ppr.odd_of_ne_two pne
      rw [Nat.odd_iff] at pne
      rw [sum_nat_mod] at mod2; have : ∑ i ∈ range (n.factorization p + 1), p ^ i % 2 =
      ∑ i ∈ range (n.factorization p + 1), 1 := by
        apply sum_congr rfl; intros; rw [Nat.pow_mod, pne]; simp
      simp [this] at mod2; omega
  -- Prove that $2$ divides $n$
    have pf2 : 2 ∈ n.primeFactors := by
      by_contra h'; replace h' : ∀ p ∈ n.primeFactors, p ≠ 2 := by
        intro p hp peq; rw [peq] at hp; contradiction
      replace mod2 : ∀ p ∈ n.primeFactors, (n.factorization p + 1) % 2 = 1 := by
        intro p hp; specialize mod2 p hp (h' p hp); omega
      rw [Nat.card_divisors, prod_nat_mod] at h
      rw [prod_congr rfl mod2] at h; simp at h
      omega
  -- Prove that the power of $2$ in $n$ is even
    replace h : n.factorization 2 % 2 = 1 := by
      rw [Nat.card_divisors, prod_nat_mod] at h
      rw [prod_eq_prod_diff_singleton_mul pf2] at h
      replace mod2 : ∀ p ∈ n.primeFactors \ {2}, (n.factorization p + 1) % 2 = 1 := by
        intro p hp; rw [mem_sdiff] at hp; rcases hp with ⟨hp, pne⟩
        simp [← ne_eq] at pne; specialize mod2 p hp pne
        omega
      simp [prod_congr rfl mod2] at h; all_goals omega
  -- Fulfill the goal with a number constructed from the prime factorization of $n$, the powers are carefully chosen so that the required equality holds true
    use 2 ^ ((n.factorization 2 - 1) / 2) * ∏ p ∈ n.primeFactors \ {2}, p ^ (n.factorization p / 2)
    rw [mul_pow, ← pow_mul, ← prod_pow, ← mul_assoc, ← pow_succ']
    have PFn := Nat.factorization_prod_pow_eq_self (show n≠0 by omega)
    simp [Finsupp.prod] at PFn; rw [prod_eq_prod_diff_singleton_mul pf2] at PFn
    nth_rw 1 [← PFn, mul_comm]; congr 1
    · nth_rw 2 [← Nat.div_add_mod (n.factorization 2) 2]
      simp [h]; rw [← h]; symm; apply Nat.div_add_mod'
    · apply prod_congr rfl; intro p hp
      rw [mem_sdiff] at hp; rcases hp with ⟨hp, pne⟩
      simp [← ne_eq] at pne; specialize mod2 p hp pne
      rw [← pow_mul, Nat.div_mul_cancel]; omega
    omega
-- In the odd case, we rewrite `h` by `aux` to show that all the powers in the prime factorization of $n$ is even
  rw [aux] at h; simp at mod2; rw [Nat.add_mod] at mod2
  replace mod2 : (∑ d ∈ n.divisors, d) % 2 = 0 := by omega
  rw [Nat.sum_divisors] at mod2
-- Compute the parity of the sum of divisors of $n$
  replace h : ∀ p ∈ n.primeFactors, (∑ k ∈ range (n.factorization p + 1), p ^ k) % 2 = 1 := by
    intro p hp; by_cases h' : p = 2
    · rw [sum_nat_mod]; simp [h']
      rw [add_comm, sum_range_add]
      simp [Nat.pow_mod, pow_succ]
    replace h' : p % 2 = 1 := by
      rw [← Nat.odd_iff]; simp at hp
      exact hp.left.odd_of_ne_two h'
    rw [sum_nat_mod]; suffices : ∑ i ∈ range (n.factorization p + 1), p ^ i % 2 =
    ∑ i ∈ range (n.factorization p + 1), 1
    · simp [this]; specialize h p hp
      omega
    apply sum_congr rfl; intros; rw [Nat.pow_mod, h']
    simp
-- Deduct a contradiction on parity and finish the rest trivial goals
  simp [prod_nat_mod, prod_congr rfl h] at mod2
  all_goals omega