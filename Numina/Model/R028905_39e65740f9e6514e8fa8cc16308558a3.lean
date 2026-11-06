import Mathlib

theorem algebra_101672 (n : ℕ) (h : n % 2 = 1) :
    ∑ i ∈ Finset.range 50, (n + 2 * i)^2 = 300850 ↔ n + 2 * 49 = 121 := by
  constructor
  · -- Assume $\sum_{i = 0}^{49} (n + 2i)^2 = 300850$, prove $n + 2 \cdot 49 = 121$.
    intro h1
    norm_num [Finset.sum_range_succ] at h1
    have h2 : n ≤ 32 := by
      nlinarith
    interval_cases n <;> omega
  · -- Assume n + 2 * 49 = 121, prove $\sum_{i = 0}^{49} (n + 2i)^2 = 300850$.
    intro h2
    have h3 : n = 23 := by
      omega
    rw [h3]
    norm_num [Finset.sum_range_succ]