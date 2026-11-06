import Mathlib

theorem algebra_60183 (n : ℕ) (h : n > 0) :
    ∑ i ∈ Finset.range n, (2 * i + 1) = 100 ↔ n = 10 := by
  constructor
  · -- Forward direction: if the sum is 100, prove n = 10
    intro h_eq
    have h_sum_eq_sq : ∀ k : ℕ, ∑ i ∈ Finset.range k, (2 * i + 1) = k ^ 2 := by
      intro k
      induction k with
      | zero =>
        simp
      | succ k ihk =>
        rw [Finset.sum_range_succ, ihk]
        ring_nf
        <;> omega
    have sum_eq_sq : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := h_sum_eq_sq n
    rw [sum_eq_sq] at h_eq
    have h10 : n ≤ 10 := by
      nlinarith
    interval_cases n <;> omega
  · -- Backward direction: if n = 10, prove the sum is 100
    intro h_eq
    rw [h_eq]
    norm_num [Finset.sum_range_succ]