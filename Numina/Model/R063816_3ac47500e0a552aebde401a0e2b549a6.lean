import Mathlib

theorem number_theory_163681 (m n : ℕ) (hm : m > 0) (hn : n > 0)
    (hsum : ∑ i ∈ Finset.range m, (2 * i + 2) + ∑ j ∈ Finset.range n, (2 * j + 1) = 1987) :
    3 * m + 4 * n ≤ 221 := by
  have h1 : ∀ m : ℕ, ∑ i in Finset.range m, (2 * i + 2) = m * (m + 1) := by 
    intro m
    induction m with
    | zero =>
      simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring_nf
      <;> omega

  have h2 : ∀ n : ℕ, ∑ j in Finset.range n, (2 * j + 1) = n * n := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring_nf
      <;> omega
  
  have h3 : m * (m + 1) + n * n = 1987 := by
    rw [h1 m, h2 n] at hsum
    omega
  
  by_contra h
  push_neg at h
  have h4 : m * (m + 1) + n * n < 1987 := by
    nlinarith [sq_nonneg (m - 27 : ℤ), sq_nonneg (n - 35 : ℤ)]
  linarith