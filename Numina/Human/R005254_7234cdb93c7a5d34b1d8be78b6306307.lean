import Mathlib

/- Soient $m, n, k$ trois entiers positifs tels que $m^{2}+n=k^{2}+k$. Montrer que $m \leqslant n$. -/
theorem number_theory_607191 (m n k : ℕ) (mpos : 0 < m) (npos : 0 < n) (kpos : 0 < k)
(heq : m^2 + n = k^2 + k) : m ≤ n := by
-- Assume the contrary that $n$ is less than $m$
  by_contra! nltm
-- It suffices to show that $2*k+1$ is strictly between $2 *m$ and $2 *m + 1$, which is absurd
  suffices : 2 * m < 2 * k + 1 ∧ 2 * k + 1 < 2 * m + 1; linarith
  constructor
  -- Taking squares on both sides of the goals and rewrite them using the assumption heq, both goals will follow
  · rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]; calc
      _ < 4 * (m ^ 2 + n) := by ring_nf; simp; exact npos
      _ < _ := by rw [heq]; ring_nf; simp [add_assoc]
    all_goals positivity
  rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]; calc
    _ = 4 * (k ^ 2 + k) + 1 := by ring
    _ < 4 * (m ^ 2 + m) + 1 := by rw [← heq]; gcongr
    _ = _ := by ring
  all_goals positivity