import Mathlib
open Finset Nat

/-Find the value of
$$
\binom{6}{1} 2^{1}+\binom{6}{2} 2^{2}+\binom{6}{3} 2^{3}+\binom{6}{4} 2^{4}+\binom{6}{5} 2^{5}+\binom{6}{6} 2^{6} .
$$-/
theorem combinatorics_23456 :
    ∑ k ∈  Finset.range 6, Nat.choose 6 (k + 1) * 2 ^ (k + 1) = 3 ^ 6 - 1 := by
  -- Recognize the sum as part of the binomial expansion of (1+2)^6.
  have h_binomial : (∑ k ∈  Finset.range 7, Nat.choose 6 k * 2 ^ k) = 3 ^ 6 := by
    simp [Finset.sum_range_succ, Nat.choose_succ_succ, pow_succ]
  -- Split the sum to isolate the first term.
  have h_full_sum : (∑ k ∈  Finset.range 7, Nat.choose 6 k * 2 ^ k) =
      Nat.choose 6 0 * 2 ^ 0 + (∑ k ∈  Finset.range 6, Nat.choose 6 (k + 1) * 2 ^ (k + 1)) := by
    rw [Finset.sum_range_succ]
    simp
    tauto
  -- Compute the first term, \binom{6}{0} 2^0 = 1.
  have h_first_term : Nat.choose 6 0 * 2 ^ 0 = 1 := by
    simp [Nat.choose_zero_right]
  -- Compute the target sum by subtracting the first term.
  have h_split : (∑ k ∈  Finset.range 6, Nat.choose 6 (k + 1) * 2 ^ (k + 1)) =
      (∑ k ∈ Finset.range 7, Nat.choose 6 k * 2 ^ k) - Nat.choose 6 0 * 2 ^ 0 := by
    rw [h_full_sum]
    simp [h_first_term]
  rw [h_split, h_binomial, h_first_term]