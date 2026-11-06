import Mathlib

theorem algebra_7001 (n : ℕ) (hn : n > 0) :
    ∑ i ∈ Finset.range n, (2 * i + 1) ≤ 100 ↔ n ≤ 10 := by
  constructor
  · -- Forward: if ∑ i in range n, (2*i + 1) ≤ 100, then n ≤ 10
    intro h
    have h1 : ∀ n : ℕ , ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    have h2 : n ^ 2 ≤ 100 := by
      have h_eq : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := (h1 n)
      linarith [h_eq, h]
    by_contra h3
    push_neg at h3
    have h4 : n ≥ 11 := by omega
    have h5 : n ^ 2 ≥ 121 := by
      nlinarith
    nlinarith
  · -- Backward: if n ≤ 10, then ∑ i in range n, (2*i + 1) ≤ 100
    intro h
    have h1 : ∀ n : ℕ , ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    have h2 : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := (h1 n)
    have h3 : n ^ 2 ≤ 100 := by
      have h4 : n ≤ 10 := h
      nlinarith
    linarith [h2, h3]