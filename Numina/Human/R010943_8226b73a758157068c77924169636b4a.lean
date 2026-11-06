import Mathlib

/-A number is the product of four prime numbers. Which is this number, if we know that the sum of the squares of the four prime numbers is 476?-/
theorem number_theory_205143 (p1 p2 p3 p4 : ℕ) (pr1 : p1.Prime) (pr2 : p2.Prime)
    (pr3 : p3.Prime) (pr4 : p4.Prime) (heq : p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + p4 ^ 2 = 476) :
    p1 * p2 * p3 * p4 = 1989 := by
-- Assume w. l. o. g. that $p1%3≤ p2%3 ≤ p3%3 ≤ p4%3$
  wlog le1 : p1 % 3 ≤ p2 % 3
  · specialize this p2 p1 p3 p4
    rw [← this]; ring; any_goals assumption
    rw [← heq]; ring; omega
  wlog le2 : p1 % 3 ≤ p3 % 3
  · specialize this p3 p2 p1 p4
    rw [← this]; ring; any_goals assumption
    rw [← heq]; ring; all_goals omega
  wlog le3 : p1 % 3 ≤ p4 % 3
  · specialize this p4 p2 p3 p1
    rw [← this]; ring; any_goals assumption
    rw [← heq]; ring; all_goals omega
  wlog le4 : p2 % 3 ≤ p3 % 3
  · specialize this p1 p3 p2 p4
    rw [← this]; ring; any_goals assumption
    rw [← heq]; ring; all_goals omega
  wlog le5 : p2 % 3 ≤ p4 % 3
  · specialize this p1 p4 p3 p2
    rw [← this]; ring; any_goals assumption
    rw [← heq]; ring; all_goals omega
  wlog le6 : p3 % 3 ≤ p4 % 3
  · specialize this p1 p2 p4 p3
    rw [← this]; ring; any_goals assumption
    rw [← heq]; ring; all_goals omega
-- Prove an auxillary lemma that if $p$, $q$ are primes whose sum of square is $458$, then $p*q$ is $221$
  have aux : ∀ p q : ℕ, p.Prime → q.Prime → p ^ 2 + q ^ 2 = 458 → p * q = 221 := by
    clear * -; intro p q ppr qpr heq; wlog h : p ≤ q
    · specialize this q p; rw [← this]; ring
      any_goals assumption
      rw [← heq]; ring; omega
    have : p ^ 2 ≤ q ^ 2 := by gcongr
    have : 15 ^ 2 < q ^ 2 := by omega
    rw [Nat.pow_lt_pow_iff_left] at this
    have : q ^ 2 < 23 ^ 2 := by omega
    rw [Nat.pow_lt_pow_iff_left] at this
    interval_cases q; all_goals norm_num at qpr
    · replace heq : p ^ 2 = 13 ^ 2 := by omega
      rw [pow_left_inj₀] at heq
      all_goals omega
    · have : p ^ 2 < 10 ^ 2 := by omega
      rw [Nat.pow_lt_pow_iff_left] at this
      have : 9 ^ 2 < p ^ 2 := by omega
      rw [Nat.pow_lt_pow_iff_left] at this
      all_goals omega
    all_goals simp
-- Discuss all possible remainders of $p1$, $p2$, $p3$, $p4$ modulo $3$
  have := Nat.mod_lt p1 (show 3>0 by simp)
  have := Nat.mod_lt p2 (show 3>0 by simp)
  have := Nat.mod_lt p3 (show 3>0 by simp)
  have := Nat.mod_lt p4 (show 3>0 by simp)
  have mod3 := heq; apply_fun fun t => t % 3 at mod3
  rw [Nat.add_mod] at mod3; nth_rw 2 [Nat.add_mod] at mod3
  nth_rw 3 [Nat.add_mod] at mod3; rw [Nat.pow_mod] at mod3
  nth_rw 2 [Nat.pow_mod] at mod3; nth_rw 3 [Nat.pow_mod] at mod3
  nth_rw 4 [Nat.pow_mod] at mod3
  interval_cases p1m3 : p1 % 3 <;> interval_cases p2m3 : p2 % 3 <;>
  interval_cases p3m3 : p3 % 3 <;> interval_cases p4m3 : p4 % 3
  all_goals norm_num at mod3
-- Show that $p1$, $p2$ must be $3$, therefore $p3^2+p4^2$ is $458$
  any_goals rw [← Nat.dvd_iff_mod_eq_zero, Nat.prime_dvd_prime_iff_eq] at p1m3
  any_goals rw [← Nat.dvd_iff_mod_eq_zero, Nat.prime_dvd_prime_iff_eq] at p2m3
  any_goals norm_num
  any_goals assumption
  any_goals norm_num [← p1m3, ← p2m3] at *; clear * - pr3 pr4 heq aux
  any_goals replace heq : p3 ^ 2 + p4 ^ 2 = 458 := by omega
-- Apply `aux` to finish the goal
  any_goals rw [mul_assoc]; nth_rw 2 [aux]; norm_num
  all_goals assumption