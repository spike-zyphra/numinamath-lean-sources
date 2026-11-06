import Mathlib

open Finset Nat

/- [ Products and factorials ] [Partitions into pairs and groups; bijections ]

Prove that if the integer $n>2$, then $(n!)^{2}>n^{n}$. -/
theorem inequalities_222255 {n : ℕ} (hn : n > 2) : (n !) ^ 2 > n ^ n := by
  rw [pow_two]
  -- Rewrite in terms of ascending factorial
  nth_rw 1 [← one_ascFactorial]
  -- Rewrite in terms of descending factorial
  rw [← descFactorial_self]
  -- Rewrite as a product over a range
  rw [ascFactorial_eq_prod_range, descFactorial_eq_prod_range, ← prod_mul_distrib]
  nth_rw 1 [show n = n - 1 + 1 by exact (Nat.sub_add_cancel (show 1 ≤ n by linarith)).symm]
  rw [prod_range_succ]
  nth_rw 1 [show n - 1 = n - 2 + 1 by simp; exact (Nat.sub_add_cancel (show 2 ≤ n by linarith)).symm]
  rw [prod_range_succ']
  simp
  -- Lower bound each factor by n
  have bound : ∀ k ∈ range (n - 2), n < (1 + (k + 1)) * (n - (k + 1)) := by
    intro k hk
    simp at hk
    rw [Nat.mul_sub, add_mul, one_mul, mul_comm _ (k + 1), Nat.add_sub_assoc, ← Nat.mul_sub]
    · -- Finish computation
      nth_rw 1 [← add_zero n]
      apply add_lt_add_left
      -- Verify positivity
      apply mul_pos (by positivity)
      rw [← add_assoc, add_comm, ← add_assoc, one_add_one_eq_two, add_comm]
      exact Nat.sub_pos_of_lt (add_lt_of_lt_sub hk)
    -- Check condition
    rw [← add_assoc, add_comm 1, add_assoc, one_add_one_eq_two]
    apply Nat.mul_le_mul_left
    linarith [add_lt_of_lt_sub hk]
  -- Continue simplifying
  rw [show 1 + (n - 1) = n by rw [add_comm]; exact Nat.sub_add_cancel (show 1 ≤ n by linarith)]
  rw [show n - (n - 1) = 1 by exact Nat.sub_sub_self (show 1 ≤ n by linarith)]
  rw [mul_one, mul_assoc, ← pow_two]
  -- Remove a factor of n^2 from both sides
  nth_rw 2 [show n = n - 2 + 2 by exact (Nat.sub_add_cancel (show 2 ≤ n by linarith)).symm]
  rw [pow_add, mul_lt_mul_right (by positivity)]
  conv_lhs => rw [show n - 2 = (range (n - 2)).card by simp, ← prod_const n]
  -- Show product is less than product factor wise
  apply prod_lt_prod
  -- Check 3 conditions that are all simple linear inequalities
  · intro i hi
    positivity
  · intro i hi
    linarith [bound i hi]
  use 0
  rw [mem_range]
  constructor
  · exact Nat.sub_pos_of_lt (hn)
  rw [Nat.mul_sub]
  simp
  rw [Nat.lt_sub_iff_add_lt]
  calc
    n + 2 < n + n := by linarith
    _ = 2 * n := by rw [two_mul]