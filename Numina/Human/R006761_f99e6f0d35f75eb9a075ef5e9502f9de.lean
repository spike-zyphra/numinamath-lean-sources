import Mathlib
/- Let $k$ be a positive integer. Let $d_e$ be a non-zero even digit (i.e., a digit from the set $\{2,4,6,8\}$) and $d_o$ be an odd digit (i.e., a digit from the set $\{1,3,5,7,9\}$). Show that there is a unique positive integer $n$ satisfying the following conditions:
1.  $n$ is written in base 10.
2.  $n$ has exactly $k$ digits.
3.  All digits of $n$ must be either $d_e$ or $d_o$.
4.  $n$ is divisible by $2^k$. -/
theorem number_theory_640866 (k d1 d2 : ℕ) (h1 : d1 ∈ ({2, 4, 6, 8} : Set ℕ)) (h2 : d2 ∈ ({1, 3, 5, 7, 9} : Set ℕ)) (hk : k > 0) : ∃! (d : ℕ → ℕ), ((∀ i ∈ Finset.range k, d i = d1 ∨ d i = d2) ∧ (∀ i ≥ k, d i = 0) ∧ (2 ^ k ∣ ∑ i in Finset.range k, d i * 10 ^ i)):= by
  clear hk
  -- Proof by induction on k
  induction k with
  | zero =>
    -- Base case: k = 0, use the zero function
    use 0
    simp
    intro y hy
    ext i
    rw [hy i]
    simp
  | succ k ih =>
    -- Inductive step: k = k + 1
    -- Get the unique function d for k digits from induction hypothesis
    rcases ih with ⟨d, ih1, ih2⟩
    -- Extract the properties of d from ih1
    rcases ih1 with ⟨h3, -, h5⟩
    -- Extract the divisibility condition: 2^k divides the sum
    rcases h5 with ⟨t, ht⟩
    -- Case analysis on whether t is odd
    by_cases g : Odd t
    .
      -- Case 1: t is odd, use odd digit d2 for the k-th position
      -- Define new function d0 that extends d with d2 at position k
      set d0:= fun i => if i < k then d i else if i = k then d2 else 0 with hd0
      clear_value d0
      use d0
      constructor
      .
        simp
        constructor
        .
          -- Show that d0 satisfies the digit constraint (only d1 or d2)
          intro i hi
          by_cases hi1 : i = k
          .
            -- If i = k, then d0 i = d2 (odd digit)
            subst i
            right
            subst hd0
            simp
          .
            -- If i < k, use the induction hypothesis
            replace hi : i < k:= by omega
            subst d0
            simp [hi]
            exact h3 i (by simp ; omega)
        .
          constructor
          .
            -- Show that d0 i = 0 for i ≥ k+1
            intro i hi
            subst d0
            simp [hi]
            have g : ¬(i < k):= by omega
            simp [g]
            intro h
            omega
          .
            -- Show that 2^(k+1) divides the sum of d0
            rw [Finset.sum_range_succ]
            -- The sum for the first k digits equals the sum for d
            have h5 : ∀ i ∈ Finset.range k, d i * 10 ^ i = d0 i * 10 ^ i:= by
              intro i hi
              subst d0
              simp at hi
              simp [hi]
            replace h5 : ∑ i in Finset.range k, d i * 10 ^ i = ∑ i in Finset.range k, d0 i * 10 ^ i:= by exact Finset.sum_congr rfl h5
            -- d0 k = d2
            have h6 : d0 k = d2:= by
              subst d0
              simp
            -- Rewrite the sum using the induction hypothesis
            rw [←h5, h6, ht]
            -- Factor out 2^k from 10^k
            rw [show 10 = 2 * 5 by simp]
            rw [show (2 * 5) ^ k = 2 ^ k * 5 ^ k by exact Nat.mul_pow 2 5 k]
            rw [show 2 ^ k * t + d2 * (2 ^ k * 5 ^ k) = 2 ^ k * (t + d2 * 5 ^ k) by ring]
            -- Show that 5^k is odd
            have g1 : Odd 5:= by decide
            replace g1 : Odd (5 ^ k):= by exact Odd.pow g1
            -- Show that d2 is odd
            replace h2 : Odd d2:= by
              simp at h2
              rcases h2 with h2 | h2 | h2 | h2 | h2
              all_goals
                rw [h2]
                decide
            -- d2 * 5^k is odd (product of two odd numbers)
            replace g1 : Odd (d2 * 5 ^ k):= by exact Odd.mul h2 g1
            -- t + d2 * 5^k is even (odd + odd = even)
            replace g : Even (t + d2 * 5 ^ k):= by exact Odd.add_odd g g1
            -- Extract the factor of 2
            rcases g with ⟨p, hp⟩
            rw [hp]
            use p
            ring
      .
        -- Show uniqueness: any other function y satisfying the conditions equals d0
        intro y hy
        rcases hy with ⟨hy1, hy2, hy3⟩
        rw [Finset.sum_range_succ] at hy3
        -- Show that 2^k divides the sum of the first k digits of y
        have hy4 : 2 ^ k ∣ ∑ x ∈ Finset.range k, y x * 10 ^ x:= by
          rw [show 2 ^ (k + 1) = 2 * 2 ^ k by ring] at hy3
          replace hy3 : 2 ^ k ∣ ∑ x ∈ Finset.range k, y x * 10 ^ x + y k * 10 ^ k:= by
            have g : 2 ^ k ∣ 2 * 2 ^ k:= by simp
            exact Nat.dvd_trans g hy3
          rw [show 10 = 2 * 5 by simp] at hy3
          rw [show (2 * 5) ^ k = 2 ^ k * 5 ^ k by exact Nat.mul_pow 2 5 k] at hy3
          have g1 : 2 ^ k ∣ y k * (2 ^ k * 5 ^ k):= by
            use y k * 5 ^ k
            ring
          exact (Nat.dvd_add_iff_left g1).mpr hy3
        -- Define z as y but with z k = 0
        set z:= fun i => if i = k then 0 else y i with hz
        clear_value z
        -- Apply induction hypothesis to z
        specialize ih2 z ⟨?_, ?_, ?_⟩
        intro i hi
        simp at hi
        subst z
        simp [show ¬(i = k) by omega]
        exact hy1 i (by simp ; omega)
        intro i hi
        by_cases hi1 : i = k
        .
          subst z i
          simp
        .
          subst z
          simp [hi1]
          exact hy2 i (by omega)
        have hz1 : ∀ i ∈ Finset.range k, z i * 10 ^ i = y i * 10 ^ i:= by
          intro i hi
          simp at hi
          subst z
          simp [show ¬(i = k) by omega]
        replace hz1 : ∑ i in Finset.range k, z i * 10 ^ i = ∑ i in Finset.range k, y i * 10 ^ i:= by exact Finset.sum_congr rfl hz1
        rw [hz1]
        exact hy4
        ext i
        by_cases hi : i ≠ k
        .
          by_cases hi1 : i < k
          .
            -- For i < k, use induction hypothesis
            subst d0
            simp [hi1]
            rw [←ih2]
            subst z
            simp [hi]
          .
            -- For i > k, both are 0
            subst d0
            simp [hi1, hi]
            exact hy2 i (by omega)
        .
          -- For i = k, show y k = d2
          simp at hi
          subst i
          subst d0
          simp
          rw [ih2] at hz
          -- Show that y equals d for first k digits
          replace hz : ∀ i ∈ Finset.range k, y i * 10 ^ i = d i * 10 ^ i:= by
            intro i hi
            rw [hz]
            simp at hi
            simp [show ¬(i = k) by omega]
          replace hz : ∑ i ∈ Finset.range k, y i * 10 ^ i = ∑ i ∈ Finset.range k, d i * 10 ^ i:= by exact Finset.sum_congr rfl hz
          -- Use the divisibility condition to show y k = d2
          rw [←hz] at ht
          rw [ht] at hy3
          rw [show 10 = 2 * 5 by simp] at hy3
          rw [show (2 * 5) ^ k = 2 ^ k * 5 ^ k by exact Nat.mul_pow 2 5 k] at hy3
          rw [show 2 ^ k * t + y k * (2 ^ k * 5 ^ k) = 2 ^ k * (t + y k * 5 ^ k) by ring] at hy3
          rw [show 2 ^ (k + 1) = 2 ^ k * 2 by ring] at hy3
          have g1 : 2 ^ k ≠ 0:= by positivity
          replace hy3 : 2 ∣ t + y k * 5 ^ k:= by exact (mul_dvd_mul_iff_left g1).mp hy3
          replace hy3 : Even (t + y k * 5 ^ k):= by exact (even_iff_exists_two_nsmul (t + y k * 5 ^ k)).mpr hy3
          replace hy1:= hy1 k (by simp)
          rcases hy1 with hy1 | hy1
          .
            -- If y k = d1 (even), then t + y k * 5^k is odd, contradiction
            replace h1 : Even d1:= by
              simp at h1
              rcases h1 with h1 | h1 | h1 | h1
              all_goals
                rw [h1]
                decide
            rw [←hy1] at h1
            replace h1 : Even (y k * 5 ^ k):= by exact Even.mul_right h1 (5 ^ k)
            replace h1 : Odd (t + y k * 5 ^ k):= by exact Even.odd_add h1 g
            absurd hy3
            simp
            exact h1
          .
            -- y k = d2, as required
            exact hy1
    .
      -- Case 2: t is even, use even digit d1 for the k-th position
      simp at g
      -- Define new function d0 that extends d with d1 at position k
      set d0:= fun i => if i < k then d i else if i = k then d1 else 0 with hd0
      clear_value d0
      use d0
      constructor
      .
        simp
        constructor
        .
          -- Show that d0 satisfies the digit constraint (only d1 or d2)
          intro i hi
          by_cases hi1 : i = k
          .
            -- If i = k, then d0 i = d1 (even digit)
            subst i
            left
            subst hd0
            simp
          .
            -- If i < k, use the induction hypothesis
            replace hi : i < k:= by omega
            subst d0
            simp [hi]
            exact h3 i (by simp ; omega)
        .
          constructor
          .
            -- Show that d0 i = 0 for i ≥ k+1
            intro i hi
            subst d0
            simp [hi]
            have g : ¬(i < k):= by omega
            simp [g]
            intro h
            omega
          .
            -- Show that 2^(k+1) divides the sum of d0
            rw [Finset.sum_range_succ]
            -- The sum for the first k digits equals the sum for d
            have h5 : ∀ i ∈ Finset.range k, d i * 10 ^ i = d0 i * 10 ^ i:= by
              intro i hi
              subst d0
              simp at hi
              simp [hi]
            replace h5 : ∑ i in Finset.range k, d i * 10 ^ i = ∑ i in Finset.range k, d0 i * 10 ^ i:= by exact Finset.sum_congr rfl h5
            -- d0 k = d1
            have h6 : d0 k = d1:= by
              subst d0
              simp
            -- Rewrite the sum using the induction hypothesis
            rw [←h5, h6, ht]
            -- Factor out 2^k from 10^k
            rw [show 10 = 2 * 5 by simp]
            rw [show (2 * 5) ^ k = 2 ^ k * 5 ^ k by exact Nat.mul_pow 2 5 k]
            rw [show 2 ^ k * t + d1 * (2 ^ k * 5 ^ k) = 2 ^ k * (t + d1 * 5 ^ k) by ring]
            -- Show that d1 is even
            replace h1 : Even d1:= by
              simp at h1
              rcases h1 with h1 | h1 | h1 | h1
              all_goals
                rw [h1]
                decide
            -- d1 * 5^k is even (even * odd = even)
            replace g1 : Even (d1 * 5 ^ k):= by exact Even.mul_right h1 (5 ^ k)
            -- t + d1 * 5^k is even (even + even = even)
            replace g : Even (t + d1 * 5 ^ k):= by exact Even.add g g1
            -- Extract the factor of 2
            rcases g with ⟨p, hp⟩
            rw [hp]
            use p
            ring
      .
        -- Show uniqueness: any other function y satisfying the conditions equals d0
        intro y hy
        rcases hy with ⟨hy1, hy2, hy3⟩
        rw [Finset.sum_range_succ] at hy3
        -- Show that 2^k divides the sum of the first k digits of y
        have hy4 : 2 ^ k ∣ ∑ x ∈ Finset.range k, y x * 10 ^ x:= by
          rw [show 2 ^ (k + 1) = 2 * 2 ^ k by ring] at hy3
          replace hy3 : 2 ^ k ∣ ∑ x ∈ Finset.range k, y x * 10 ^ x + y k * 10 ^ k:= by
            have g : 2 ^ k ∣ 2 * 2 ^ k:= by simp
            exact Nat.dvd_trans g hy3
          rw [show 10 = 2 * 5 by simp] at hy3
          rw [show (2 * 5) ^ k = 2 ^ k * 5 ^ k by exact Nat.mul_pow 2 5 k] at hy3
          have g1 : 2 ^ k ∣ y k * (2 ^ k * 5 ^ k):= by
            use y k * 5 ^ k
            ring
          exact (Nat.dvd_add_iff_left g1).mpr hy3
        -- Define z as y but with z k = 0
        set z:= fun i => if i = k then 0 else y i with hz
        clear_value z
        -- Apply induction hypothesis to z
        specialize ih2 z ⟨?_, ?_, ?_⟩
        intro i hi
        simp at hi
        subst z
        simp [show ¬(i = k) by omega]
        exact hy1 i (by simp ; omega)
        intro i hi
        by_cases hi1 : i = k
        .
          subst z i
          simp
        .
          subst z
          simp [hi1]
          exact hy2 i (by omega)
        have hz1 : ∀ i ∈ Finset.range k, z i * 10 ^ i = y i * 10 ^ i:= by
          intro i hi
          simp at hi
          subst z
          simp [show ¬(i = k) by omega]
        replace hz1 : ∑ i in Finset.range k, z i * 10 ^ i = ∑ i in Finset.range k, y i * 10 ^ i:= by exact Finset.sum_congr rfl hz1
        rw [hz1]
        exact hy4
        ext i
        by_cases hi : i ≠ k
        .
          by_cases hi1 : i < k
          .
            -- For i < k, use induction hypothesis
            subst d0
            simp [hi1]
            rw [←ih2]
            subst z
            simp [hi]
          .
            -- For i > k, both are 0
            subst d0
            simp [hi1, hi]
            exact hy2 i (by omega)
        .
          -- For i = k, show y k = d1
          simp at hi
          subst i
          subst d0
          simp
          rw [ih2] at hz
          -- Show that y equals d for first k digits
          replace hz : ∀ i ∈ Finset.range k, y i * 10 ^ i = d i * 10 ^ i:= by
            intro i hi
            rw [hz]
            simp at hi
            simp [show ¬(i = k) by omega]
          replace hz : ∑ i ∈ Finset.range k, y i * 10 ^ i = ∑ i ∈ Finset.range k, d i * 10 ^ i:= by exact Finset.sum_congr rfl hz
          -- Use the divisibility condition to show y k = d1
          rw [←hz] at ht
          rw [ht] at hy3
          rw [show 10 = 2 * 5 by simp] at hy3
          rw [show (2 * 5) ^ k = 2 ^ k * 5 ^ k by exact Nat.mul_pow 2 5 k] at hy3
          rw [show 2 ^ k * t + y k * (2 ^ k * 5 ^ k) = 2 ^ k * (t + y k * 5 ^ k) by ring] at hy3
          rw [show 2 ^ (k + 1) = 2 ^ k * 2 by ring] at hy3
          have g1 : 2 ^ k ≠ 0:= by positivity
          replace hy3 : 2 ∣ t + y k * 5 ^ k:= by exact (mul_dvd_mul_iff_left g1).mp hy3
          replace hy3 : Even (t + y k * 5 ^ k):= by exact (even_iff_exists_two_nsmul (t + y k * 5 ^ k)).mpr hy3
          replace hy1:= hy1 k (by simp)
          rcases hy1 with hy1 | hy1
          .
            -- y k = d1, as required
            exact hy1
          .
            -- If y k = d2 (odd), then t + y k * 5^k is odd, contradiction
            replace h2 : Odd d2:= by
              simp at h2
              rcases h2 with h2 | h2 | h2 | h2 | h2
              all_goals
                rw [h2]
                decide
            have g2 : Odd 5:= by decide
            replace g2 : Odd (5 ^ k):= by exact Odd.pow g2
            rw [←hy1] at h2
            replace h2 : Odd (y k * 5 ^ k):= by exact Odd.mul h2 g2
            replace g2 : Odd (t + y k * 5 ^ k):= by exact Even.add_odd g h2
            absurd hy3
            simp
            exact g2
