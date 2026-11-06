import Mathlib

theorem algebra_194027 (n : ℕ) (hn : n > 0) (h : ∑ i ∈ Finset.range n, (i + 1) = 7 * n) :
    n = 13 := by
  have h2 : ∀ n : ℕ, ∑ i in Finset.range n, (i + 1) = n * (n + 1) / 2 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring_nf
      omega
  have h3 : n * (n + 1) / 2 = 7 * n := by 
    have h_eq1 : ∑ i in Finset.range n, (i + 1) = n * (n + 1) / 2 := h2 n
    rw [h_eq1] at h 
    omega 
  have h4 : n ≤ 14 := by
    by_contra h
    push_neg at h 
    have h5 : n ≥ 15 := by omega
    have h6 : n * (n + 1) / 2 > 7 * n := by
      have eq1 : n * (n + 1) ≥ 14 * n + 2 := by 
        nlinarith [h5, sq_nonneg (n : ℕ), sq_nonneg ((n : ℕ) - 15)]
      have h7 : n * (n + 1) ≥ 14 * n + 2 := by
        omega
      have h8 : n * (n + 1) / 2 > 7 * n := by
        omega
      exact h8
    have h7 : n * (n + 1) / 2 > 7 * n := h6
    omega 
  have h5 : n ≥ 13 := by
    by_contra h
    push_neg at h
    have h6 : n ≤ 12 := by omega
    have h7 : n * (n + 1) / 2 < 7 * n := by
      interval_cases n <;> omega
    have h8 : n * (n + 1) / 2 < 7 * n := h7
    omega 
  have h9 : n = 13 ∨ n = 14 := by 
    omega 
  rcases h9 with (h10 | h10)
  · exact h10
  · -- For n = 14, check hypothesis
    rw [h10] at h3 
    all_goals omega