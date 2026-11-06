import Mathlib

theorem algebra_260312 {n : ℕ} (hn : n > 0) :
    ∑ i in Finset.range n, (3 * (i + 1)^2 - 3 * (i + 1) + 1) =
    ∑ i in Finset.range n, (2 * (i + 1) + 89) ↔ n = 10 := by 
  constructor
  · -- Forward: if the sums are equal, then n = 10
    intro h_eq
    have h_eq2 : (∑ i in Finset.range n, (3 * (i + 1) ^ 2 - 3 * (i + 1) + 1) : ℕ) = (∑ i in Finset.range n, (2 * (i + 1) + 89) : ℕ) := by 
      simpa using h_eq 
    have h_eq3 : n ^ 3 = n ^ 2 + 90 * n := by
      have h1 : ∀ (n : ℕ), ∑ i in Finset.range n, (3 * (i + 1) ^ 2 - 3 * (i + 1) + 1 : ℕ) = n ^ 3 := by
        intro n 
        induction n with 
        | zero => 
          simp 
        | succ n ih => 
          rw [Finset.sum_range_succ, ih]
          ring_nf 
          <;> omega 
      have h2 : ∀ (n : ℕ), ∑ i in Finset.range n, (2 * (i + 1) + 89 : ℕ) = n ^ 2 + 90 * n := by
        intro n 
        induction n with 
        | zero => 
          simp 
        | succ n ih => 
          rw [Finset.sum_range_succ, ih]
          ring_nf 
          <;> omega 
      have h3 := h1 n
      have h4 := h2 n 
      rw [h3] at h_eq2 
      rw [h4] at h_eq2 
      nlinarith 
    by_cases h10 : n ≤ 32
    · -- Assume n ≤ 32, need to show n=10 by checking each case
      interval_cases n <;> omega 
    · -- Assume n > 32, need to derive contradiction
      have h11 : n > 32 := by
        omega 
      -- Assume n > 32, then n^3 > n^2 + 90*n
      have h12 : n ^ 3 > n ^ 2 + 90 * n := by 
        have h13 : n ≥ 33 := by 
          omega 
        have h14 : n ^3 ≥ (n ^ 2 + 90 * n + 1) := by 
          nlinarith [sq_nonneg (n - 32 : ℤ), sq_nonneg (n - 10 : ℤ), sq_nonneg (n ^ 2 - n - 90), sq_nonneg (n : ℤ)]
        omega 
      -- Contradicts with h_eq3: n^3 = n^2 + 90n
      have h13 : n ^3 = n ^2 + 90 * n := h_eq3 
      linarith [h13, h12] 
  · -- Backward: n = 10, then the sums are equal
    intro h_eq 
    rw [h_eq] 
    all_goals 
      native_decide 
  all_goals 
    try linarith