import Mathlib
set_option linter.unusedVariables false

/-Let $T$ denote the number of coins determined tails and $H$ denote the number of coins determined heads at the end of the game. Let $p_{m}(k)$ be the probability that $|T-H|=k$ after a game with $4 m$ coins, assuming that the player follows the optimal strategy outlined in problem 6. Clearly $p_{m}(k)=0$ if $k$ is an odd integer, so we need only consider the case when $k$ is an even integer. (By definition, $p_{0}(0)=1$ and $p_{0}(k)=0$ for $\left.k \geq 1\right)$. Prove that $p_{m}(0) \geq p_{m+1}(0)$ for all nonnegative integers $m$.-/
theorem combinatorics_608870 {p : ℕ → ℕ → ℝ}
    (hp0 : p 0 0 = 1)
    (hp0k : ∀ k ≠ 0, p 0 k = 0)
    (hp1 : ∀ m k, k % 2 = 1 → p m k = 0)
    (hp2 : ∀ m k, k % 2 = 0 → p (m + 1) k = p m k * (3 : ℝ) / 4 + p m (k + 2) * (1 : ℝ) / 4) :
    ∀ m, p m 0 ≥ p (m + 1) 0 := by
  -- Prove the decreasing property: $p m k ≥ p m (k + 2)$ for even $k$.
  have h_decreasing : ∀ m, ∀ k : ℕ, k % 2 = 0 → p m k ≥ p m (k + 2) := by
    intro m
    induction' m with m ih
    · intro k hk
      cases' Nat.eq_zero_or_pos k with hz hp
      · rw [hz]
        rw [hp0]
        simp
        rw [hp0k 2 (by norm_num:2 ≠ 0)]
        linarith
      · have hk : k ≠ 0 := by omega
        rw [hp0k k hk]
        have hk2 : k + 2 ≠ 0 := by omega
        rw [hp0k (k + 2) hk2]
    · intro k hk
      rw [hp2 m k hk, hp2 m (k + 2) (by omega)]
      have h_pos3 : 0 < (3 : ℝ) / 4 := by linarith
      have h_pos1 : 0 < (1 : ℝ) / 4 := by linarith
      have ih_k : p m k ≥ p m (k + 2) := ih k hk
      have ih_k2 : p m (k + 2) ≥ p m (k + 4) := ih (k + 2) (by omega)
      linarith
  -- show $p m 0 ≥ p (m + 1) 0$ using recursion and decreasing property.
  intro m
  rw [hp2 m 0 (by simp)]
  -- Use the decreasing property for $k=0$ to get $p m 0 ≥ p m 2$.
  have h_le_2 : p m 0 ≥ p m 2  := (h_decreasing m 0 (by simp)).le
  -- Positive coefficient for the term.
  have h_pos1 : 0 ≤ (1 : ℝ) / 4 := by linarith
  linarith [mul_le_mul_of_nonneg_left h_le_2 h_pos1]
