import Mathlib

open Real

theorem number_theory_5004
    (S : ℕ → ℝ)
    (hS : ∀ n, S n = ∑ i ∈ Finset.Icc 1 n, (1 / i))
    (ε : ℝ)
    (hε : 0 < ε ∧ ε < 1) :
    ∃ n, 0 < n ∧ (S n) % 1 ≤ ε := by
  use 1
  constructor
  · norm_num  -- shows that $0 < 1$.
  · -- we need to show that $0 \le \varepsilon$ by calculating $(s_n) \% 1$ at $n = 1$
    have h1 : S 1 = (1 : ℝ) := by
      rw [hS 1]
      norm_num [Finset.sum_singleton]
    rw [h1]
    have h2 : ((1 : ℝ) : ℝ) % 1 = (0 : ℝ) := by
      norm_num
    rw [h2]
    linarith -- proves that $0 \le \varepsilon$ from the hypothesis $0 < \varepsilon$