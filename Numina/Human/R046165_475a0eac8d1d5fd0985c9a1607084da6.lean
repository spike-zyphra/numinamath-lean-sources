import Mathlib

/-The director of a marching band wishes to place the members into a formation that includes all of them and has no unfilled positions. If they are arranged in a square formation, there are 5 members left over. The director realizes that if he arranges the group in a formation with 7 more rows than columns, there are no members left over. Find the maximum number of members this band can have.-/
theorem number_theory_13905 : IsGreatest {s > 0 | ∃ k, s = k^2 + 5 ∧ ∃ n, s = n * (n + 7)} 294 := by
  constructor
  · -- Prove: 294 is in the set.
    simp
    constructor
    · use 17
      norm_num
    · use 14
  · apply mem_upperBounds.mpr
    simp
    intro s hs k hk n hn
    by_cases h: n > 14
    . -- If $n > 14$ then $n^2 + 6n + 14 < n^2 + 7n < n^2 + 8n + 21$
      -- and so $(n + 3)^2 + 5 < n(n + 7) < (n + 4)^2 + 5$.
      have e₁ : (n + 3)^2 + 5 < n * (n + 7) := by
        linarith
      have e₂ : n * (n + 7) < (n + 4)^2 + 5 := by
        linarith
      rw [hn.symm, hk] at e₁ e₂
      simp at e₁ e₂
      have e₁ : n + 3 < k := by
        exact lt_of_pow_lt_pow_left' 2 e₁
      have e₂ : k < n + 4 := by
        exact lt_of_pow_lt_pow_left' 2 e₂
      -- If $n$ is an integer there are no numbers which are 5 more than a perfect square strictly between $(n + 3)^2 + 5$ and $(n + 4)^2 + 5$.
      linarith
    simp at h
    have : 294 = 14 * 21 := by linarith
    rw [this, hn]
    exact Nat.mul_le_mul h (by linarith)
