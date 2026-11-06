import Mathlib
/- Suppose that $2^{2n+1}+ 2^{n}+1=x^{k}$, where $k\geq2$ and $n$ are positive integers. Find all possible values of $n$. -/
theorem algebra_39264 : {n : ℕ | n > 0 ∧ (∃ x k : ℕ, k ≥ 2 ∧ 2 ^ (2 * n + 1) + 2 ^ n + 1 = x ^ k)} = {4}:= by
  ext n
  constructor
  .
    -- Forward direction: if n is in the set, then n = 4
    intro h
    simp at h
    rcases h with ⟨hn, x, k, hk, h⟩
    -- Case analysis on whether k is even or odd
    by_cases h1 : Even k
    .
      -- Case 1: k is even, so k = 2k' for some k'
      rcases h1 with ⟨k, rfl⟩
      rw [show k + k = k * 2 by ring] at hk h
      simp at hk
      -- Rewrite x^(2k') as (x^k')^2
      rw [show x ^ (k * 2) = (x ^ k) ^ 2 by exact Nat.pow_mul x k 2] at h
      set m:= x ^ k
      clear_value m
      -- Show that m > 0
      have h1 : m > 0:= by
        by_contra H
        simp at H
        subst m
        simp at h
      clear hk k
      set k:= m - 1 with hk
      clear_value k
      replace hk : m = k + 1:= by omega
      subst m
      ring_nf at h
      -- Rewrite 2^(2n) as (2^n)^2
      rw [show 2 ^ (n * 2) = (2 ^ n) ^ 2 by exact Nat.pow_mul 2 n 2] at h
      replace h : 2 ^ n * (2 * 2 ^ n + 1) = k * (k + 2):= by linarith
      -- Show that k must be even
      replace h1 : Even k:= by
        by_contra H
        simp at H
        have g : Even 2:= by decide
        replace g : Odd (k + 2):= by exact Even.odd_add g H
        replace H : Odd (k * (k + 2)):= by exact Odd.mul H g
        replace g : Even (2 ^ n):= by
          have g : Even 2:= by decide
          refine (Nat.even_pow' (by omega)).mpr g
        absurd H
        simp
        rw [←h]
        exact Even.mul_right g (2 * 2 ^ n + 1)
      rcases h1 with ⟨k, rfl⟩
      rw [show (k + k) * (k + k + 2) = 4 * k * (k + 1) by ring] at h
      -- Show that n ≥ 2
      replace hn : n ≥ 2:= by
        by_contra H
        replace H : n = 1:= by omega
        subst n
        simp at h
        replace h : 4 ∣ 10:= by
          use k * (k + 1)
          linarith
        omega
      set m:= n - 2 with hm
      clear_value m
      replace hm : n = m + 2:= by omega
      subst n
      rw [show 2 ^ (m + 2) = 4 * 2 ^ m by ring] at h
      replace h : 2 ^ m * (8 * 2 ^ m + 1) = k * (k + 1):= by linarith
      -- Case analysis on whether k is even or odd
      by_cases h1 : Even k
      .
        -- Subcase: k is even
        have h2 : Odd (k + 1):= by exact Even.add_one h1
        replace h2 : Nat.Coprime 2 (k + 1):= by exact Nat.coprime_two_left.mpr h2
        replace h2 : Nat.Coprime (2 ^ m) (k + 1):= by exact Nat.Coprime.pow_left m h2
        -- Show that 2^m divides k
        replace h2 : 2 ^ m ∣ k:= by
          have h3 : 2 ^ m ∣ k * (k + 1):= by rw [←h] ; simp
          exact Nat.Coprime.dvd_of_dvd_mul_right h2 h3
        rcases h2 with ⟨s, hk⟩
        rw [hk] at h
        replace h : (8 * 2 ^ m + 1) = s * (2 ^ m * s + 1):= by
          rw [show 2 ^ m * s * (2 ^ m * s + 1) = 2 ^ m * (s * (2 ^ m * s + 1)) by ring] at h
          have g : 2 ^ m > 0:= by positivity
          exact Nat.eq_of_mul_eq_mul_left g h
        subst k
        -- Show that s < 3
        replace h1 : s < 3:= by
          by_contra H
          simp at H
          have H1 : 2 ^ m * s ≥ 2 ^ m * 3:= by exact Nat.mul_le_mul_left (2 ^ m) H
          replace H1 : 2 ^ m * s + 1 ≥ 2 ^ m * 3 + 1:= by linarith
          replace H1 : s * (2 ^ m * s + 1) ≥ 3 * (2 ^ m * 3 + 1):= by exact Nat.mul_le_mul H H1
          omega
        replace h1 : s = 0 ∨ s = 1 ∨ s = 2:= by omega
        rcases h1 with rfl | rfl | rfl
        .
          -- Case s = 0: contradiction
          simp at h
        .
          -- Case s = 1: contradiction
          simp at h
        .
          -- Case s = 2: contradiction
          omega
      .
        -- Subcase: k is odd
        simp at h1
        replace h1:= Nat.coprime_two_left.mpr h1
        replace h1:= Nat.Coprime.pow_left m h1
        -- Show that 2^m divides k + 1
        replace h1 : 2 ^ m ∣ k + 1:= by
          suffices 2 ^ m ∣ k * (k + 1) by exact Nat.Coprime.dvd_of_dvd_mul_left h1 this
          rw [←h]
          simp
        rcases h1 with ⟨s, hk⟩
        rw [hk] at h
        replace h : 8 * 2 ^ m + 1 = k * s:= by
          rw [show k * (2 ^ m * s) = 2 ^ m * (k * s) by ring] at h
          have g : 2 ^ m > 0:= by positivity
          exact Nat.eq_of_mul_eq_mul_left g h
        replace h : 8 * 2 ^ m + 1 + s = (k + 1) * s:= by linarith
        rw [hk] at h
        -- Show that s is odd
        have h1 : Odd s:= by
          replace h : s ∣ 8 * 2 ^ m + 1:= by
            suffices s ∣ 8 * 2 ^ m + 1 + s by exact Nat.dvd_add_self_right.mp this
            rw [h]
            use 2 ^ m * s
            ring
          have h1 : Odd (8 * 2 ^ m + 1):= by
            use 4 * 2 ^ m
            ring
          exact Odd.of_dvd_nat h1 h
        -- Show that s < 4
        have h3 : s < 4:= by
          by_contra H
          simp at H
          have H1 : 2 ^ m * 4 ≤ 2 ^ m * s:= by exact Nat.mul_le_mul_left (2 ^ m) H
          have H2:= Nat.mul_le_mul_right s H1
          have H3 : 2 ^ m > 0:= by positivity
          replace H3 : 2 ^ m ≥ 1:= by omega
          replace H3:= Nat.mul_le_mul_right s H3
          linarith
        rcases h1 with ⟨s, rfl⟩
        replace h3 : s = 0 ∨ s = 1:= by omega
        rcases h3 with rfl | rfl
        .
          -- Case s = 0: contradiction
          simp at h
          omega
        .
          -- Case s = 1: leads to m = 2, so n = 4
          simp at h
          replace h : 2 ^ m = 2 ^ 2:= by linarith
          replace h : Nat.log 2 (2 ^ m) = Nat.log 2 (2 ^ 2):= by rw [h]
          rw [Nat.log_pow (by omega) _] at h
          rw [Nat.log_pow (by omega) _] at h
          subst m
          simp
    .
      -- Case 2: k is odd
      simp at h1
      rw [show 2 ^ (2 * n + 1) + 2 ^ n = 2 ^ n * (2 * 2 ^ n + 1) by ring] at h
      -- Show that x must be odd
      have hx : Odd x:= by
        by_contra H
        simp at H
        replace H : Even (x ^ k):= by refine (Nat.even_pow' (by omega)).mpr H
        rw [←h] at H
        have h2 : Even (2 ^ n * (2 * 2 ^ n + 1)):= by
          suffices Even (2 ^ n) by exact Even.mul_right this (2 * 2 ^ n + 1)
          suffices Even 2 by refine (Nat.even_pow' (by omega)).mpr this
          decide
        absurd H
        simp
        exact Even.add_one h2
      -- Use geometric sum formula: x^n - 1 = (x-1) * sum(x^i for i < n)
      have h2 : ∀ x : ℤ, ∀ n : ℕ, x ^ n - 1 = (x - 1) * (∑ i in Finset.range n, x ^ i):= by
        intro x n
        exact Eq.symm (mul_geom_sum x n)
      replace h2:= h2 x k
      replace h2 : x ^ k - 1 = (x - 1) * (∑ i in Finset.range k, x ^ i):= by
        replace hx : x ≠ 0:= by exact Nat.ne_of_odd_add hx
        replace hx : x ≥ 1:= by omega
        replace hx1 : x ^ k ≥ 1:= by omega
        zify
        field_simp
        exact h2
      replace h : 2 ^ n * (2 * 2 ^ n + 1) = x ^ k - 1:= by omega
      rw [h2] at h
      -- Show that the sum is odd for odd k
      have h3 : ∀ n : ℕ, Odd (∑ i ∈ Finset.range (2 * n + 1), x ^ i):= by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by omega]
          rw [Finset.sum_range_succ]
          rw [Finset.sum_range_succ]
          have g1 : Odd (x ^ (2 * n + 2)):= by exact Odd.pow hx
          have g2 : Odd (x ^ (2 * n + 1)):= by exact Odd.pow hx
          suffices Even (∑ x_1 ∈ Finset.range (2 * n + 1), x ^ x_1 + x ^ (2 * n + 1)) by exact Even.add_odd this g1
          suffices Odd (∑ x_1 ∈ Finset.range (2 * n + 1), x ^ x_1) by exact Odd.add_odd ih g2
          exact ih
      rcases h1 with ⟨k, rfl⟩
      replace h3:= h3 k
      replace h3:= Nat.coprime_two_left.mpr h3
      replace h3:= Nat.Coprime.pow_left n h3
      -- Show that 2^n divides x - 1
      replace h3 : 2 ^ n ∣ x - 1:= by
        suffices 2 ^ n ∣ 2 ^ n * (2 * 2 ^ n + 1) by rw [h] at this ; exact Nat.Coprime.dvd_of_dvd_mul_right h3 this
        simp
      rcases h3 with ⟨s, hs⟩
      rw [hs] at h
      replace h : 2 * 2 ^ n + 1 = s * ∑ i ∈ Finset.range (2 * k + 1), x ^ i:= by
        rw [show 2 ^ n * s * ∑ i ∈ Finset.range (2 * k + 1), x ^ i = 2 ^ n * (s * ∑ i ∈ Finset.range (2 * k + 1), x ^ i) by ring] at h
        have g : 2 ^ n > 0:= by positivity
        exact Nat.eq_of_mul_eq_mul_left g h
      -- Show that s ≥ 1
      have hs1 : s ≥ 1:= by
        by_contra H
        simp at H
        subst s
        simp at h
      -- Show that x - 1 ≥ 2^n
      replace hs : x - 1 ≥ 2 ^ n:= by
        have g : 2 ^ n * s ≥ 2 ^ n:= by exact Nat.le_mul_of_pos_right (2 ^ n) hs1
        linarith
      -- Show that x ≥ 2^n + 1
      replace hs : x ≥ 2 ^ n + 1:= by
        have g : 2 ^ n > 0:= by positivity
        omega
      replace hs1:= Nat.le_mul_of_pos_left (∑ i ∈ Finset.range (2 * k + 1), x ^ i) hs1
      rw [←h] at hs1
      -- Show that the sum is at least the sum of first 3 terms
      have h3 : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 3), x ^ i ≥ ∑ i ∈ Finset.range 3, x ^ i:= by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          rw [show n + 1 + 3 = n + 3 + 1 by omega]
          rw [Finset.sum_range_succ]
          omega
      replace h3:= h3 (2 * k - 2)
      rw [show 2 * k - 2 + 3 = 2 * k + 1 by omega] at h3
      replace h3 : 2 * 2 ^ n + 1 ≥ ∑ i ∈ Finset.range 3, x ^ i:= by linarith
      simp [Finset.sum_range_succ] at h3
      -- Use the inequality x^2 + 1 ≥ 2x
      have h4 : x ^ 2 + 1 ≥ 2 * x:= by
        zify
        linarith [sq_nonneg ((↑x : ℤ) - 1)]
      omega
  .
    -- Backward direction: if n = 4, then n is in the set
    intro h
    simp at h
    subst n
    simp
    -- Provide the witness: x = 23, k = 2
    use 23, 2
    simp
