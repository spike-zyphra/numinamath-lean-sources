import Mathlib

theorem number_theory_136078 (m n : ℕ) (hm : m > 0) (hn : n > 0)
    (h : ∑ i ∈ Finset.range (4 * m), (2 * i + 2) + ∑ i ∈ Finset.range n, (2 * i + 1) = 1987) :
    3 * m + 4 * n ≤ 221 := by

  have h1 : ∀ m : ℕ, ∑ i ∈ Finset.range (4 * m), (2 * i + 2) = (4 * m) * (4 * m + 1) := by
    intro m
    have h2 : ∀ m : ℕ, ∑ i ∈ Finset.range (4 * m), (2 * i + 2) = (4 * m) * (4 * m + 1) := by 
      intro m
      induction m with
      | zero =>
        simp
      | succ m ih =>
        rw [show 4 * (m + 1) = 4 * m + 4 by ring]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        simp [ih, add_assoc, mul_add, add_mul]
        all_goals ring_nf <;> omega
    specialize h2 m
    simpa using h2

  have h2 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
    intro n
    have h3 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by 
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        <;> ring_nf <;> omega
    specialize h3 n
    simpa using h3
  have h3 : (4 * m) * (4 * m + 1) + n ^ 2 = 1987 := by
    have h4 : ∑ i ∈ Finset.range (4 * m), (2 * i + 2) = (4 * m) * (4 * m + 1) := h1 m
    have h5 : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := h2 n
    linarith [h4, h5, h]
  have h6 : m ≤ 11 := by
    nlinarith [sq_nonneg (n), sq_nonneg (4 * m + 1), h3]
  have h7 : n ≤ 44 := by
    nlinarith [sq_nonneg (4 * m + 1), sq_nonneg (n), h3]
  interval_cases m <;> interval_cases n <;> omega