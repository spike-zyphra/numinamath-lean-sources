import Mathlib

theorem algebra_264751 (a : ℕ → ℤ) (ha : ∀ n, a n = 113 - 4 * n) :
    IsGreatest {∑ i in Finset.range n, a i | n} 1653 := by
  constructor
  · -- Show 1653 in the set
    use 29
    norm_num [Finset.sum_range_succ, ha]
  · -- Show greatest
    intro s hs
    rcases hs with ⟨n, hn⟩
    have h1 : ∀ n : ℕ, ∑ i in Finset.range n, a i = 115 * n - 2 * n ^ 2 := by
      intro n
      induction n with
      | zero =>
        simp [ha]
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp [ha]
        <;> ring_nf <;> omega
    have eq1 : ∑ i in Finset.range n, a i = 115 * n - 2 * n ^ 2 := h1 n
    have h2 : (115 * n - 2 * n ^ 2 : ℤ) ≤ 1653 := by
      by_contra h
      push_neg at h
      have h3 : n ≥ 30 := by
        by_contra h4
        push_neg at h4
        interval_cases n <;> omega
      nlinarith [ sq_nonneg ( (n : ℤ) - 29 ) ]
    have eq2 : ∑ i in Finset.range n, a i ≤ 1653 := by
      linarith [ eq1, h2 ]
    linarith [ eq1, h2, hn ]