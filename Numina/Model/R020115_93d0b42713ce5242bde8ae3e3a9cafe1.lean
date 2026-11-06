import Mathlib

theorem algebra_308784 (n : ℕ) (hn : n ≥ 5) (a : ℕ → ℝ)
    (h1 : ∀ i, i + 4 < n → ∑ j ∈ Finset.range 5, a (i + j) < 0)
    (h2 : ∀ i, i + 8 < n → ∑ j ∈ Finset.range 9, a (i + j) > 0) :
    n ≤ 12 := by
  by_contra h
  push_neg at h
  have h3 : n ≥ 13 := by omega
  have h4 : ∑ j in Finset.range 5, a (0 + j) < 0 := by
    apply h1 0
    omega
  have h5 : ∑ j in Finset.range 5, a (1 + j) < 0 := by
    apply h1 1
    omega
  have h6 : ∑ j in Finset.range 5, a (2 + j) < 0 := by
    apply h1 2
    omega
  have h7 : ∑ j in Finset.range 5, a (3 + j) < 0 := by
    apply h1 3
    omega
  have h8 : ∑ j in Finset.range 5, a (4 + j) < 0 := by
    apply h1 4
    omega
  have h9 : ∑ j in Finset.range 5, a (5 + j) < 0 := by
    apply h1 5
    omega
  have h10 : ∑ j in Finset.range 5, a (6 + j) < 0 := by
    apply h1 6
    omega
  have h11 : ∑ j in Finset.range 5, a (7 + j) < 0 := by
    apply h1 7
    omega
  have h12 : ∑ j in Finset.range 5, a (8 + j) < 0 := by
    apply h1 8
    omega
  -- Now derive positivity from h2 for indices 0 to 4
  have h13 : ∑ j in Finset.range 9, a (0 + j) > 0 := by
    apply h2 0
    omega
  have h14 : ∑ j in Finset.range 9, a (1 + j) > 0 := by
    apply h2 1
    omega
  have h15 : ∑ j in Finset.range 9, a (2 + j) > 0 := by
    apply h2 2
    omega
  have h16 : ∑ j in Finset.range 9, a (3 + j) > 0 := by
    apply h2 3
    omega
  have h17 : ∑ j in Finset.range 9, a (4 + j) > 0 := by
    apply h2 4
    omega
  -- Now we have all these constraints as 14 inequalities, from which we need to derive a contradiction.
  simp [Finset.sum_range_succ] at h4 h5 h6 h7 h8 h9 h10 h11 h12
  simp [Finset.sum_range_succ] at h13 h14 h15 h16 h17
  linarith