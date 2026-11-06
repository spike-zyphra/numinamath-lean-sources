import Mathlib
/- Let $k_0=1$. Find all positive integers $n$ for which the sum $S_n = 1^3 + 2^3 + \dots + n^3$ is divisible by $n+3$. Show that the set of such positive integers $n$ is $\{3, 6, 15\}$. -/
theorem algebra_637843 : {n : ℕ | n > 0 ∧ n + 3 ∣ ∑ i in Finset.range n, (i + 1) ^ 3} = {3, 6, 15}:= by
  -- Prove set equality by showing membership in both directions
  ext n
  constructor
  -- Forward direction: if n satisfies the condition, then n ∈ {3, 6, 15}
  .
    intro h
    simp at h
    rcases h with ⟨h1, h2⟩
    -- Key lemma: the formula for sum of cubes is 4 * S_n = n^2 * (n+1)^2
    have h3 : ∀ n : ℕ, 4 * ∑ i ∈ Finset.range n, (i + 1) ^ 3 = n ^ 2 * (n + 1) ^ 2:= by
      intro n
      -- Prove by induction on n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ]
        linarith
    specialize h3 n
    -- If (n+3) divides S_n, then 4*(n+3) divides 4*S_n
    replace h2 : 4 * (n + 3) ∣ 4 * (∑ i ∈ Finset.range n, (i + 1) ^ 3):= by exact Nat.mul_dvd_mul_left 4 h2
    -- Substitute the formula for sum of cubes
    rw [h3] at h2
    -- Show that n+3 must divide 36
    have h4 : n + 3 ∣ 36:= by
      zify
      -- Remove factor of 4 from divisibility condition
      replace h2 : n + 3 ∣ n ^ 2 * (n + 1) ^ 2:= by exact dvd_of_mul_left_dvd h2
      zify at h2
      -- Use polynomial identity to show n+3 divides 36
      rw [show (↑n : ℤ) ^ 2 * (↑n + 1) ^ 2 = (n * (n + 1) + 6) * (n - 2) * (n + 3) + 36 by linarith] at h2
      suffices (↑n : ℤ) + 3 ∣ (↑n * (↑n + 1) + 6) * (↑n - 2) * (↑n + 3) by exact (Int.dvd_iff_dvd_of_dvd_add h2).mp this
      simp
    -- Compute all divisors of 36
    have h5 : Nat.divisors 36 = {1, 2, 3, 4, 6, 9, 12, 18, 36}:= by native_decide
    -- n+3 must be a divisor of 36
    replace h4 : n + 3 ∈ Nat.divisors 36:= by refine Nat.mem_divisors.mpr ⟨h4, by omega⟩
    rw [h5] at h4
    simp at h4
    -- Case analysis on possible values of n+3
    rcases h4 with h4 | h4 | h4 | h4 | h4 | h4 | h4
    -- For each case, solve for n and verify the divisibility condition
    all_goals
      subst n
      simp at h2
      simp
    -- Use omega to eliminate impossible cases
    all_goals
      omega
  -- Backward direction: if n ∈ {3, 6, 15}, then n satisfies the condition
  .
    intro h
    simp at h
    -- Case analysis on the three possible values
    rcases h with h | h | h
    -- For each case, verify that n+3 divides the sum of cubes
    all_goals
      subst n
      simp [Finset.sum_range_succ]
      omega
