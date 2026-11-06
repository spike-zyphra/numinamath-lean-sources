import Mathlib
/- Let $N$ be a positive integer. Let $k$ be a natural number and $m$ be an odd natural number.
Prove that the sum $\sum_{i=1}^{N} (ik)^m$ is a multiple of the sum $\sum_{i=1}^{N} ik$. -/
theorem algebra_642235 (n k m : ℕ) (hn : n > 0) (hm : Odd m) : ∑ i in Finset.range n, ((i + 1) * k) ∣ ∑ i in Finset.range n, ((i + 1) * k) ^ m:= by
  -- Case analysis: when k = 0
  by_cases hk : k = 0
  .
    -- If k = 0, substitute and simplify
    subst k
    simp
    right
    exact Nat.ne_of_odd_add hm
  .
    -- Factor out k from the first sum
    rw [show ∑ i ∈ Finset.range n, (i + 1) * k = (∑ i ∈ Finset.range n, (i + 1)) * k by exact Eq.symm (Finset.sum_mul (Finset.range n) (fun i => i + 1) k)]
    -- Distribute the power over multiplication for each term
    have h : ∀ i ∈ Finset.range n, ((i + 1) * k) ^ m = (i + 1) ^ m * k ^ m:= by
      intro i _
      exact Nat.mul_pow (i + 1) k m
    -- Apply the distribution to the entire sum
    rw [show ∑ i ∈ Finset.range n, ((i + 1) * k) ^ m = ∑ i ∈ Finset.range n, ((i + 1) ^ m * k ^ m) by exact Finset.sum_congr rfl h]
    -- Factor out k^m from the sum
    rw [show ∑ i ∈ Finset.range n, ((i + 1) ^ m * k ^ m) = (∑ i ∈ Finset.range n, (i + 1) ^ m) * k ^ m by exact Eq.symm (Finset.sum_mul (Finset.range n) (fun i => (i + 1) ^ m) (k ^ m))]
    -- Key lemma: 2 times the sum equals sum of symmetric terms
    have h0 : ∀ n : ℕ, 2 * ∑ i ∈ Finset.range n, ((↑i : ℤ) + 1) ^ m = ∑ i ∈ Finset.range n, (((↑i : ℤ) + 1) ^ m + (n - (↑i : ℤ)) ^ m):= by
      intro n
      -- Handle the case when n = 0
      by_cases hn : n = 0
      .
        subst n
        simp
      .
        -- Split the sum into two parts
        rw [show ∑ i ∈ Finset.range n, (((↑i : ℤ) + 1) ^ m +(n - (↑i : ℤ)) ^ m) = ∑ i ∈ Finset.range n, ((↑i : ℤ) + 1) ^ m + ∑ i ∈ Finset.range n, (n - (↑i : ℤ)) ^ m by exact Finset.sum_add_distrib]
        -- Show that the two parts are equal
        suffices ∑ i ∈ Finset.range n, ((i : ℤ) + 1) ^ m = ∑ i ∈ Finset.range n, (n - (i : ℤ)) ^ m by linarith
        -- Define function f for cleaner notation
        set f : ℕ → ℤ:= fun x => ((↑x : ℤ) + 1) ^ m with hf
        clear_value f
        -- Use sum flip to show symmetry
        have g1 : ∑ x ∈ Finset.range (n - 1 + 1), f x = ∑ x ∈ Finset.range (n - 1 + 1), f (n - 1 - x):= by exact Eq.symm (Finset.sum_flip f)
        rw [show n - 1 + 1 = n by omega] at g1
        -- Show that f(n-1-x) = (n-x)^m
        have g2 : ∀ x ∈ Finset.range n, f (n - 1 - x) = (n - (x : ℤ)) ^ m:= by
          intro x hx
          simp [hf]
          simp at hx
          rw [show n - 1 - x = n - (1 + x) by omega]
          replace hx : n ≥ 1 + x:= by omega
          field_simp
          ring_nf
        -- Apply the transformation to the sum
        replace g2 : ∑ x ∈ Finset.range n, f (n - 1 - x) = ∑ x ∈ Finset.range n, (n - (x : ℤ)) ^ m:= by exact Finset.sum_congr rfl g2
        rw [g2] at g1
        rw [←g1]
    -- k divides k^m since k is non-zero
    have h1 : k ∣ k ^ m:= by exact dvd_pow_self k (by exact Nat.ne_of_odd_add hm)
    -- Main goal: show that sum of (i+1) divides sum of (i+1)^m
    suffices ∑ i ∈ Finset.range n, (i + 1) ∣ ∑ i ∈ Finset.range n, (i + 1) ^ m by exact Nat.mul_dvd_mul this h1
    -- 2 is non-zero
    have g : 2 ≠ 0:= by omega
    -- Multiply both sides by 2 to use the symmetric sum property
    suffices 2 * ∑ i ∈ Finset.range n, (i + 1) ∣ 2 * ∑ i ∈ Finset.range n, (i + 1) ^ m by exact (mul_dvd_mul_iff_left g).mp this
    clear g h1 h hk k
    -- Formula for 2 times the sum of consecutive integers
    have h1 : ∀ n : ℕ, 2 * ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1):= by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ]
        linarith
    rw [h1 n]
    -- n and n+1 are coprime
    replace h1 : Nat.Coprime n (n + 1):= by refine Nat.coprime_self_add_right.mpr (by simp)
    -- Key congruence: sum of symmetric terms is divisible by n+1
    have h2 : ∀ k n : ℕ, ∑ i ∈ Finset.range k, ((i + 1) ^ m + (n - i) ^ m) ≡ 0 [ZMOD n + 1]:= by
      intro k n
      induction k with
      | zero =>
        simp
      | succ k ih =>
        rw [Finset.sum_range_succ]
        rw [show (0 : ℤ) = 0 + 0 by simp]
        -- Show that each pair of symmetric terms sums to 0 mod n+1
        suffices (↑k + 1) ^ m + (↑n - ↑k) ^ m ≡ 0 [ZMOD n + 1] by exact Int.ModEq.add ih this
        rw [show (↑n : ℤ) - k = n + 1 + (-1) * (k + 1) by omega]
        -- Use modular arithmetic properties
        have g : n + 1 + (-1) * (k + 1) ≡ (-1) * (k + 1) [ZMOD n + 1]:= by exact Int.add_modEq_left
        replace g:= Int.ModEq.pow m g
        rw [show (-1 * ((↑k : ℤ) + 1)) ^ m = (-1) ^ m * ((↑k : ℤ) + 1) ^ m by exact mul_pow (-1) ((↑k : ℤ) + 1) m] at g
        -- Since m is odd, (-1)^m = -1
        rw [show (-1) ^ m = -1 by exact Odd.neg_one_pow hm] at g
        replace g : (↑k + 1) ^ m + (↑n + 1 + -1 * (↑k + 1)) ^ m ≡ (↑k + 1) ^ m + -1 * (↑k + 1) ^ m [ZMOD ↑n + 1]:= by exact Int.ModEq.add rfl g
        rw [show ((↑k : ℤ) + 1) ^ m + -1 * (↑k + 1) ^ m = 0 by ring_nf] at g
        exact g
    -- n+1 divides 2 times the sum of (i+1)^m
    have h3 : n + 1 ∣ 2 * ∑ i ∈ Finset.range n, (i + 1) ^ m:= by
      zify
      rw [h0 n]
      replace h2:= h2 n n
      exact Int.dvd_of_emod_eq_zero h2
    -- n divides 2 times the sum of (i+1)^m (case analysis on parity of n)
    have h4 : n ∣ 2 * ∑ i ∈ Finset.range n, (i + 1) ^ m:= by
      by_cases h4 : Odd n
      .
        -- Case 1: n is odd
        rcases h4 with ⟨k, rfl⟩
        rw [Finset.sum_range_succ]
        rw [show 2 * (∑ x ∈ Finset.range (2 * k), (x + 1) ^ m + (2 * k + 1) ^ m) = 2 * (∑ x ∈ Finset.range (2 * k), (x + 1) ^ m) + 2 * (2 * k + 1) ^ m by ring]
        -- 2k+1 divides (2k+1)^m
        have g : 2 * k + 1 ∣ (2 * k + 1) ^ m:= by exact dvd_pow_self (2 * k + 1) (by exact Nat.ne_of_odd_add hm)
        replace g : 2 * k + 1 ∣ 2 * (2 * k + 1) ^ m:= by exact Dvd.dvd.mul_left g 2
        -- Show that 2k+1 divides the remaining sum
        suffices 2 * k + 1 ∣ 2 * ∑ x ∈ Finset.range (2 * k), (x + 1) ^ m by exact (Nat.dvd_add_iff_right this).mp g
        zify
        rw [h0 (2 * k)]
        simp
        -- Use the congruence property
        suffices ∑ x ∈ Finset.range (2 * k), ((↑x + 1) ^ m + (2 * (↑k : ℤ) - ↑x) ^ m) ≡ 0 [ZMOD 2 * k + 1] by exact Int.dvd_of_emod_eq_zero this
        specialize h2 (2 * k) (2 * k)
        simp at h2
        exact h2
      .
        -- Case 2: n is even
        simp at h4
        rcases h4 with ⟨t, ht⟩
        rw [show t + t = 2 * t by omega] at ht
        set k:= t - 1 with hk
        clear_value k
        replace hk : t = k + 1:= by omega
        subst t
        subst n
        -- Show that k+1 divides the sum
        suffices (k + 1) ∣ ∑ i ∈ Finset.range (2 * (k + 1)), (i + 1) ^ m by exact Nat.mul_dvd_mul_left 2 this
        rw [show 2 * (k + 1) = 2 * k + 2 by omega]
        rw [Finset.sum_range_succ]
        rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
        -- k+1 divides (2(k+1))^m
        replace g : k + 1 ∣ (2 * (k + 1)) ^ m:= by
          have g : k + 1 ∣ 2 * (k + 1):= by simp
          have g1 : 2 * (k + 1) ∣ (2 * (k + 1)) ^ m:= by exact dvd_pow_self (2 * (k + 1)) (by exact Nat.ne_of_odd_add hm)
          exact Nat.dvd_trans g g1
        -- Show that k+1 divides the remaining sum
        suffices k + 1 ∣ ∑ x ∈ Finset.range (2 * k + 1), (x + 1) ^ m by exact (Nat.dvd_add_iff_right this).mp g
        -- Break down the sum into parts
        have h4 : ∀ n : ℕ, ∑ i ∈ Finset.range (k + 1 + n), (i + 1) ^ m = ∑ i ∈ Finset.range k, (i + 1) ^ m + ∑ i ∈ Finset.range n, (k + 2 + i) ^ m + (k + 1) ^ m:= by
          intro n
          induction n with
          | zero =>
            simp
            rw [Finset.sum_range_succ]
          | succ n ih =>
            rw [show k + 1 + (n + 1) = k + 1 + n + 1 by omega]
            rw [Finset.sum_range_succ]
            rw [Finset.sum_range_succ]
            rw [show k + 1 + n + 1 = k + 2 + n by omega]
            linarith
        replace h4:= h4 k
        rw [show k + 1 + k = 2 * k + 1 by omega] at h4
        rw [h4]
        -- k+1 divides (k+1)^m
        replace g : k + 1 ∣ (k + 1) ^ m:= by exact dvd_pow_self (k + 1) (by exact Nat.ne_of_odd_add hm)
        -- Show that k+1 divides the sum of the two parts
        suffices k + 1 ∣ ∑ i ∈ Finset.range k, (i + 1) ^ m + ∑ i ∈ Finset.range k, (k + 2 + i) ^ m by exact (Nat.dvd_add_iff_right this).mp g
        -- Show that the two parts are congruent modulo k+1
        replace g : ∑ i ∈ Finset.range k, (k + 2 + i) ^ m ≡ ∑ i ∈ Finset.range k, (i + 1) ^ m [MOD k + 1]:= by
          replace g : ∀ n : ℕ, ∑ i ∈ Finset.range n, (k + 2 + i) ^ m ≡ ∑ i ∈ Finset.range n, (i + 1) ^ m [MOD k + 1]:= by
            intro n
            induction n with
            | zero =>
              simp
              rfl
            | succ n ih =>
              rw [Finset.sum_range_succ]
              rw [Finset.sum_range_succ]
              -- Show that corresponding terms are congruent
              suffices (k + 2 + n) ^ m ≡ (n + 1) ^ m [MOD k + 1] by exact Nat.ModEq.add ih this
              suffices k + 2 + n ≡ n + 1 [MOD k + 1] by exact Nat.ModEq.pow m this
              rw [show n + 1 = 0 + (n + 1) by simp]
              rw [show k + 2 + n = k + 1 + (n + 1) by omega]
              suffices k + 1 ≡ 0 [MOD k + 1] by exact Nat.ModEq.add_right (n + 1) this
              suffices k + 1 ∣ k + 1 by exact Nat.ModEq.symm (Dvd.dvd.zero_modEq_nat this)
              simp
          exact g k
        -- Combine the congruence with the sum
        replace g : ∑ i ∈ Finset.range k, (i + 1) ^ m + ∑ i ∈ Finset.range k, (k + 2 + i) ^ m ≡ ∑ i ∈ Finset.range k, (i + 1) ^ m + ∑ i ∈ Finset.range k, (i + 1) ^ m [MOD k + 1]:= by exact Nat.ModEq.add_left (∑ i ∈ Finset.range k, (i + 1) ^ m) g
        rw [show ∑ i ∈ Finset.range k, (i + 1) ^ m + ∑ i ∈ Finset.range k, (i + 1) ^ m = 2 * ∑ i ∈ Finset.range k, (i + 1) ^ m by ring] at g
        -- Show that the sum is divisible by k+1
        suffices ∑ i ∈ Finset.range k, (i + 1) ^ m + ∑ i ∈ Finset.range k, (k + 2 + i) ^ m ≡ 0 [MOD k + 1] by exact Nat.dvd_of_mod_eq_zero this
        suffices 2 * ∑ i ∈ Finset.range k, (i + 1) ^ m ≡ 0 [MOD k + 1] by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm this)) (id (Nat.ModEq.symm g)))
        suffices k + 1 ∣ 2 * ∑ i ∈ Finset.range k, (i + 1) ^ m by exact Nat.modEq_zero_iff_dvd.mpr this
        zify
        -- Use the symmetric sum property
        suffices 2 * ∑ i ∈ Finset.range k, ((↑i : ℤ) + 1) ^ m ≡ 0 [ZMOD k + 1] by exact Int.dvd_of_emod_eq_zero this
        rw [h0 k]
        exact h2 k k
    -- Final step: use coprimality to combine the divisibility results
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h1 h4 h3
