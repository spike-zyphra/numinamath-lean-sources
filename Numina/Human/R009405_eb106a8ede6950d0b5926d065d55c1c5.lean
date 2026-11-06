import Mathlib

/-- What is the largest positive integer that is not the sum of a positive integral multiple of 42
    42 and a positive composite integer? -/
theorem number_theory_96403 :
    IsGreatest {n | 0 < n ∧ ¬∃ k m : ℕ, 0 < k ∧ n = 42 * k + m ∧ m > 0 ∧ ¬Nat.Prime m} 215 := by
  constructor
  -- 215 is such a number (we will later show it is the greatest);
  · simp only [gt_iff_lt, exists_and_left, not_exists, not_and, Decidable.not_not,
    Set.mem_setOf_eq, Nat.ofNat_pos, true_and]
    intro x pos k eq pos2
    -- Let 215 = 42x + k, x, k > 0, then clearly, x < 6.
    have : x < 6 := by
      by_contra h
      rw[not_lt] at h
      linarith
    -- Then, there are only 5 possibilites for x, which imply k = 173,131,89,47,5 respectively,
    -- but all of these numbers are prime.
    interval_cases x
    · obtain rfl : k = 173 := by linarith
      norm_num
    · obtain rfl : k = 131 := by linarith
      norm_num
    · obtain rfl : k = 89 := by linarith
      norm_num
    · obtain rfl : k = 47 := by linarith
      norm_num
    · obtain rfl : k = 5 := by linarith
      norm_num
  -- Now let k be a number with this property,
  · rintro k ⟨kpos, nex⟩
    push_neg at nex
    rw[← not_lt]
    intro lt
    -- and 215 < k. We rewrite k = k/42 + k % 42, where / denotes rounding down divison.
    rw[← Nat.div_add_mod k 42] at *
    -- By the assumed inequality, 4 < k/42.
    have : 4 < k / 42 := by
      rw[lt_iff_not_le]
      intro le
      have : k % 42 < 42 := Nat.mod_lt _ (by simp)
      linarith
    -- To show 42 is not a divisor of k,
    -- we can apply the property to 42 * ((k/42) - 1) and 42, since if 42 divided k,
    -- 42 * ((k/42) - 1) + 42 = k would hold, but 42 is composite, contradiction.
    have : k % 42 ≠ 0 := by
      intro eq
      rw[eq] at nex
      specialize nex ((k / 42) - 1) 42 (by omega) (by omega) (by simp)
      norm_num at nex
    -- Similarly, we can show that for all b < k/42, 42b + k % 42 must be prime, since its difference to k
    -- is a multiple of 42.
    have below_prime (b) (hb : b < k / 42) : Nat.Prime (42 * b + k % 42) := by
      apply nex (k/42 - b) _ (by rwa[Nat.sub_pos_iff_lt])
      · rw[Nat.mul_sub]
        omega
      · omega
    -- Since 4 < k/42, this shows that k % 42, k % 42 + 42, k % 42 + 84 and k % 42 + 126 must be prime.
    have : k % 42 < 42 := Nat.mod_lt _ (by simp)
    have prime0 : Nat.Prime (k % 42) := by convert below_prime 0 (by linarith) using 1; simp
    have prime1 : Nat.Prime (42 + k % 42) := by convert below_prime 1 (by linarith) using 1
    have prime2 : Nat.Prime (84 + k % 42) := by convert below_prime 2 (by linarith) using 1
    have prime3 : Nat.Prime (126 + k % 42) := by convert below_prime 3 (by linarith) using 1
    have ⟨le,ge⟩ : 0 <= k % 42 ∧ k % 42 < 42 := by omega
    -- We use brute force to show that there is only one such case.
    have mod_eq : k % 42 = 5 := by
      interval_cases k % 42
      -- The primes between 126 and 126 + 42 are precisely
      -- 127,131,137,139,149,151,157,163,167.
      any_goals norm_num at prime3
      -- Going down one multiple of 42, these correspond to
      -- 85,89,95,97,107,109,115,121,125
      -- of which only 89,97,107,109 remain prime.
      any_goals norm_num at prime2
      -- These correspond to 47, 55, 65, 67, of which only 47 and 67 are prime.
      any_goals norm_num at prime1
      -- These correspond to 5 and 25, of which only 5 is prime. So k % 42 = 5.
      any_goals norm_num at prime0
      any_goals simp
    -- So our number is of the form k / 42 + 5. Since (k-1) / 42 + 5 and so on must be prime
    -- and 215 is not, we can see that 215 is indeed the maximum possible value.
    have : k / 42 < 6 := by
      rw[lt_iff_not_le]
      intro le
      specialize below_prime 5 (lt_of_lt_of_le (Nat.lt_succ_self _) le)
      rw[mod_eq] at below_prime
      norm_num at below_prime
    linarith