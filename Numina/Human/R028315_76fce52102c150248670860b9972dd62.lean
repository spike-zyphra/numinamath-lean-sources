import Mathlib

open Nat

/- ## Task A-4.2.

Determine all ordered pairs $(p, n)$, where $p$ is a prime and $n$ is a natural number, for which


$$

1+p+p^{2}+p^{3}+\cdots+p^{n}=2801

$$
 -/
theorem number_theory_210632 (p n : ℕ) (hp : Nat.Prime p) :
    (∑ i ∈ Finset.range (n + 1), p ^ i) = 2801 ↔ (p, n) = (7, 4) := by
  constructor
  · -- Prove that (7, 4) is the only solution
    intro h
    have p_sub_one_pos : 0 < p - 1 := by apply Nat.sub_pos_of_lt; linarith [Prime.two_le hp]
    -- Split off the 1
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by linarith)] at h
    apply Nat.eq_sub_of_add_eq' at h
    simp at h
    -- Use geometric series sum formula
    have geomsum : _ := geomSum_eq (Prime.two_le hp) (n + 1)
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by linarith)] at geomsum
    apply Nat.eq_sub_of_add_eq' at geomsum
    norm_num at geomsum
    -- Multiply by p - 1 on both sides
    rw [← Nat.mul_right_inj (show p - 1 ≠ 0 by linarith [p_sub_one_pos]), h] at geomsum
    -- Simplify the RHS
    have : _ := nat_sub_dvd_pow_sub_pow p 1 (n + 1)
    rw [one_pow] at this
    conv_rhs at geomsum =>
      -- Simplify fractions
      rw [Nat.mul_sub, ← Nat.mul_div_assoc _ this, Nat.mul_div_cancel_left _ p_sub_one_pos]
      rw [mul_one, Nat.sub_sub, Nat.add_sub_cancel' (by linarith [Prime.two_le hp])]
      -- Factor out a p
      rw [pow_add, pow_one, mul_comm]
      rhs
      rw [← mul_one p]
    rw [← Nat.mul_sub] at geomsum
    -- We must have p ∣ 2800
    have p_dvd_2800 : p ∣ 2800 := by
      have : p ∣ (p - 1) * 2800 := by rw [geomsum]; simp
      rw [Nat.Prime.dvd_mul hp] at this
      -- Show that p doesn't divide p - 1
      have : ¬ p ∣ p - 1 := not_dvd_of_pos_of_lt p_sub_one_pos (Nat.sub_lt_self (by positivity) (by linarith [Prime.two_le hp]))
      tauto
    -- Show that p is 2, 5, or 7
    have p_values : p = 2 ∨ p = 5 ∨ p = 7 := by
      -- Find the prime factors of 2800
      have : primeFactors 2800 = {2, 5, 7} := by
        -- Factor 2800
        have : 2800 = 2 ^ 4 * 5 ^ 2 * 7 := by norm_num
        rw [this]
        repeat rw [primeFactors_mul (by positivity)]
        rw [primeFactors_prime_pow (by positivity) prime_two]
        rw [primeFactors_prime_pow (by positivity) prime_five]
        rw [Prime.primeFactors (show Nat.Prime 7 by norm_num)]
        decide
        all_goals positivity
      -- Use primeFactors to deduce
      suffices p ∈ ({2, 5, 7} : Finset ℕ) by
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        tauto
      rw [← this, mem_primeFactors_of_ne_zero (by positivity)]
      exact ⟨hp, p_dvd_2800⟩
    -- Show that n is positive
    have : 0 < n := by
      contrapose! geomsum
      have : n = 0 := by linarith
      rw [this]
      norm_num
      linarith
    -- Casework on whether p is 2, 5, or 7
    rcases p_values with rfl | rfl | rfl
    · -- Show that 2 is impossible
      exfalso
      norm_num at geomsum
      rw [show 2800 = 2 * 1400 by norm_num] at geomsum
      apply Nat.eq_of_mul_eq_mul_left (by positivity) at geomsum
      -- Show that n is positive
      -- Use a parity argument to get a contradiction
      have : Even 1400 := by decide
      have : Odd (2 ^ n - 1) := by
        apply Nat.Even.sub_odd
        · exact one_le_pow n 2 (by positivity)
        · exact (even_pow' (show n ≠ 0 by linarith)).mpr even_two
        exact odd_one
      rw [← geomsum, ← not_even_iff_odd] at this
      tauto
    · -- Show that 5 is impossible by mod 5
      exfalso
      norm_num at geomsum
      rw [show 11200 = 5 * 2240 by norm_num] at geomsum
      apply Nat.eq_of_mul_eq_mul_left (by positivity) at geomsum
      symm at geomsum
      rw [Nat.sub_eq_iff_eq_add (one_le_pow n 5 (by positivity))] at geomsum
      have : 5 ∣ 5 ^ n := dvd_pow_self _ (by linarith)
      have : ¬ 5 ∣ 2240 + 1 := by norm_num
      rw [← geomsum] at this
      tauto
    · -- Show that n = 4 for p = 7
      simp
      norm_num at geomsum
      rw [show 16800 = 7 * 2400 by norm_num] at geomsum
      apply Nat.eq_of_mul_eq_mul_left (by positivity) at geomsum
      symm at geomsum
      rw [Nat.sub_eq_iff_eq_add (one_le_pow n 7 (by positivity))] at geomsum
      norm_num at geomsum
      -- Use contraposition
      contrapose! geomsum
      -- Casework on whether n is less than or greater than 4
      have n_cases : n < 4 ∨ 4 < n := Nat.lt_or_lt_of_ne geomsum
      rcases n_cases with hn | hn
      · -- Show that when n < 4, manually check the values to see that none work
        interval_cases n
        all_goals
        norm_num
      -- Use the fact that 7 ^ 4 < 7 ^ n to show that none work
      have : 7 ^ 4 = 2401 := by norm_num
      have : 7 ^ 4 < 7 ^ n := Nat.pow_lt_pow_of_lt (by norm_num) hn
      linarith
  -- Show that the solution (7, 4) works
  rintro ⟨hp, hn⟩
  norm_num