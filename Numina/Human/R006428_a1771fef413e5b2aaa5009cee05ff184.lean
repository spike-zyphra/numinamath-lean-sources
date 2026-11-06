import Mathlib
/- Let $m$ be an integer such that $m \ge 2$. Let $N = 2^m$. Consider the set of the first $N/2$ positive odd integers. These are $1, 3, 5, \dots, N-1$. Show that the sum of their multiplicative inverses modulo $N$, when taken modulo $N$, is $0$. -/
theorem number_theory_636947 (m : ℕ) (hm : m ≥ 2) (d : ℕ → ℤ) (hd : ∀ k : ℕ, k < 2 ^ (m - 1) → d k * (2 * k + 1) ≡ 1 [ZMOD 2 ^ m]) : ∑ k ∈ Finset.range (2 ^ (m - 1)), d k ≡ 0 [ZMOD 2 ^ m]:= by
  -- Set n = m - 2 and clear its value for later use
  set n:= m - 2 with hn
  clear_value n
  -- Replace m with n + 2 using the relationship
  replace hn : m = n + 2:= by omega
  subst m
  clear hm
  -- Simplify the exponent in the hypothesis and goal
  rw [show n + 2 - 1 = n + 1 by omega] at hd ⊢
  -- Set N = 2^n and clear its value
  set N:= 2 ^ n with hN
  clear_value N
  -- Rewrite 2^(n+1) as 2*N in hypothesis and goal
  rw [show 2 ^ (n + 1) = 2 * N by subst N ; ring_nf] at hd ⊢
  -- Key insight: sum over range equals sum over flipped range
  have h1 : ∑ x ∈ Finset.range (N - 1 + 1), d x = ∑ x ∈ Finset.range (N - 1 + 1), d (N - 1 - x):= by exact Eq.symm (Finset.sum_flip d)
  -- Prove N is positive
  have hNpos : N > 0:= by subst N ; positivity
  -- Simplify the range expression
  rw [show N - 1 + 1 = N by omega] at h1
  -- Split the sum into two parts: first N terms and next N terms
  have h2 : ∑ k ∈ Finset.range (2 * N), d k = ∑ k ∈ Finset.range N, d k + ∑ k ∈ Finset.range N, d (k + N):= by
    -- General lemma: sum over range(N + m) equals sum over range(N) plus sum over range(m) with offset N
    have h2 : ∀ m : ℕ, ∑ k ∈ Finset.range (N + m), d k = ∑ k ∈ Finset.range N, d k + ∑ k ∈ Finset.range m, d (k + N):= by
      intro m
      -- Prove by induction on m
      induction m with
      | zero =>
        simp
      | succ m ih =>
        -- Use sum_range_succ to add the next term
        rw [Finset.sum_range_succ]
        rw [show N + (m + 1) = N + m + 1 by omega]
        rw [Finset.sum_range_succ]
        rw [show m + N = N + m by omega]
        linarith
    -- Apply the general lemma with m = N
    specialize h2 N
    rw [show N + N = 2 * N by omega] at h2
    exact h2
  -- Substitute the flipped sum into the equation
  rw [h1] at h2
  -- Combine the two sums using sum_add_distrib
  rw [show ∑ x ∈ Finset.range N, d (N - 1 - x) + ∑ k ∈ Finset.range N, d (k + N) = ∑ x ∈ Finset.range N, (d (N - 1 - x) + d (x + N)) by exact Eq.symm Finset.sum_add_distrib] at h2
  rw [h2]
  -- Key step: prove that each pair of terms sums to 0 modulo 2^(n+2)
  have h3 : ∀ x ∈ Finset.range N, d (N - 1 - x) + d (x + N) ≡ 0 [ZMOD 2 ^ (n + 2)]:= by
    intro x hx
    simp at hx
    -- Get the multiplicative inverse properties for both terms
    have g1:= hd (N - 1 - x) (by omega)
    have g2:= hd (x + N) (by omega)
    simp at g1 g2
    -- Simplify the index expression
    rw [show N - 1 - x = N - (1 + x) by omega] at g1
    have g : N ≥ 1 + x:= by omega
    field_simp at g1
    -- Rewrite the modulus as 4*N
    rw [show (2 : ℤ) ^ (n + 2) = 4 * N by subst N ; simp ; ring_nf] at g1 g2 ⊢
    -- Multiply the first congruence by -1
    replace g1 : d (N - (1 + x)) * (2 * (↑N - (1 + ↑x)) + 1) * (-1) ≡ 1 * (-1) [ZMOD 4 * N]:= by exact Int.ModEq.mul g1 rfl
    -- Simplify the left side of the congruence
    rw [show d (N - (1 + x)) * (2 * (↑N - (1 + ↑x)) + 1) * -1 = d (N - (1 + x)) * (2 * x + 1 - 2 * N) by linarith] at g1
    simp at g1
    -- Prove that the second term's coefficient is congruent to the first term's coefficient
    have g3 : 2 * (↑x + ↑N) + 1 ≡ 2 * x + 1 - 2 * N [ZMOD 4 * N]:= by
      rw [show 2 * (x + (↑N : ℤ)) + 1 = 2 * x + 1 + 2 * N by linarith]
      rw [show 2 * x + 1 - 2 * (↑N : ℤ) = 2 * x + 1 + -2 * N by linarith]
      -- Show that 2*N ≡ -2*N (mod 4*N)
      suffices 2 * N ≡ -2 * N [ZMOD 4 * N] by exact Int.ModEq.add rfl this
      suffices 4 * (↑N : ℤ) ∣ 2 * (↑N : ℤ) - (-2 * (↑N : ℤ)) by exact Int.ModEq.mul_right' rfl
      ring_nf
      simp
    -- Apply the congruence to the second term
    replace g3 : d (x + N) * (2 * (↑x + ↑N) + 1) ≡ d (x + N) * (2 * x + 1 - 2 * N) [ZMOD 4 * N]:= by exact Int.ModEq.mul rfl g3
    -- Use transitivity to get the desired form for the second term
    replace g2 : d (x + N) * (2 * ↑x + 1 - 2 * ↑N) ≡ 1 [ZMOD 4 * N]:= by exact Int.ModEq.trans (id (Int.ModEq.symm g3)) g2
    -- Add the two congruences
    replace g1:= Int.ModEq.add g1 g2
    simp at g1
    -- Factor out the common term
    rw [show d (N - (1 + x)) * (2 * ↑x + 1 - 2 * ↑N) + d (x + N) * (2 * ↑x + 1 - 2 * ↑N) = (d (N - (1 + x)) + d (x + N)) * (2 * ↑x + 1 - 2 * ↑N) by linarith] at g1
    -- Convert to divisibility form
    replace g1 : 4 * (↑N : ℤ) ∣ (d (N - (1 + x)) + d (x + N)) * (2 * ↑x + 1 - 2 * ↑N):= by exact Int.dvd_of_emod_eq_zero g1
    -- Prove that the coefficient is coprime with 4*N
    have g4 : IsCoprime (4 * (↑N : ℤ)) (2 * ↑x + 1 - 2 * ↑N):= by
      subst N
      simp
      rw [show (4 : ℤ) * 2 ^ n = 2 ^ (n + 2) by ring_nf]
      -- Show that 2 is coprime with the coefficient
      suffices IsCoprime (2 : ℤ) (2 * ↑x + 1 - 2 * 2 ^ n) by exact IsCoprime.pow_left this
      use (2 ^ n - x), 1
      linarith
    -- Use coprimality to conclude that 4*N divides the sum
    suffices 4 * (↑N : ℤ) ∣ d (N - 1 - x) + d (x + N) by exact Int.ModEq.symm (Dvd.dvd.zero_modEq_int this)
    rw [show N - 1 - x = N - (1 + x) by omega]
    exact IsCoprime.dvd_of_dvd_mul_right g4 g1
  -- Extend the result to partial sums by induction
  replace h3 : ∀ m : ℕ, m ≤ N → ∑ x ∈ Finset.range m, (d (N - 1 - x) + d (x + N)) ≡ 0 [ZMOD 2 ^ (n + 2)]:= by
    intro m hm
    -- Prove by induction on m
    induction m with
    | zero =>
      simp
    | succ m ih =>
      -- Apply induction hypothesis
      replace ih:= ih (by omega)
      rw [Finset.sum_range_succ]
      -- Add the next term using the base case
      replace h3:= h3 m (by simp ; omega)
      replace ih:= Int.ModEq.add ih h3
      simp at ih
      exact ih
  -- Apply the result to the full sum
  exact h3 N (by omega)
