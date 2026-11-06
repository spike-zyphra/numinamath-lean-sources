import Mathlib

open Nat

/- Show that there are infinitely many prime numbers.-/
theorem number_theory_4480 (n : ℕ) : ∃ p > n, p.Prime := by
--   Consider the integer defined as
-- $$Q_{n} = n! + 1, \quad n \geqslant 1$$
  set m : ℕ := n ! + 1 with hm
  have hm_ne_one : m ≠ 1 := by
    rw [hm]
    apply Nat.ne_of_gt
    simp
    apply Nat.factorial_pos
  -- According to Lemma 1.1, we know that $Q_{n}$ has at least one prime divisor, which we will denote as $q_{n}$.
  obtain ⟨p, ⟨hp, hpn⟩⟩ := Nat.exists_prime_and_dvd hm_ne_one
  use p
  refine ⟨?_, hp⟩
  --  It follows that $q_{n}$ must be greater than $n$. To understand why, assume for the sake of contradiction that $q_{n} \leq n$. If this were true, then $q_{n}$ would divide $n!$ (since $n!$ is the product of all integers from 1 to $n$). However, by Proposition 1.4, we have that $q_{n}$ also divides the difference $Q_{n} - n!$, which simplifies to $1$. This leads to the conclusion that $q_{n}$ divides $1$, which is impossible since the only divisor of 1 is 1 itself, and 1 is not a prime number.
  by_contra h
  push_neg at h
  have hp_dvd : p ∣ n ! := Nat.dvd_factorial hp.pos h
  apply Nat.mod_eq_zero_of_dvd at hp_dvd
  apply Nat.mod_eq_zero_of_dvd at hpn
  apply_fun (· % p) at hm
  conv_rhs at hm =>
    rw [Nat.add_mod, hp_dvd, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt <| hp.two_le]
  linarith
