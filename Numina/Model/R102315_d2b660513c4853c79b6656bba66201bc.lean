import Mathlib

theorem number_theory_198003 (m n : ℕ) (hm : m > 0) (hn : n > 0)
    (hsum : ∑ i ∈ Finset.range m, (2 * i + 2) + ∑ i ∈ Finset.range n, (2 * i + 1) = 1987) :
    3 * m + 4 * n ≤ 221 := by
  have h1 : ∀ m : ℕ, ∑ i in Finset.range m, (2 * i + 2) = m * (m + 1) := by
    intro m
    induction m with
    | zero =>
      simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have h2 : ∀ n : ℕ, ∑ i in Finset.range n, (2 * i + 1) = n * n := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring_nf
  have sum_eq1 : ∑ i ∈ Finset.range m, (2 * i + 2) = m * (m + 1) := h1 m
  have sum_eq2 : ∑ i ∈ Finset.range n, (2 * i + 1) = n * n := h2 n
  rw [sum_eq1, sum_eq2] at hsum

  by_cases h : m ≤ 40
  · interval_cases m <;> try { norm_num [mul_add] at hsum <;> try { 
      have : n ≤ 45 := by nlinarith
      interval_cases n <;> omega
    }
  }
  · -- m > 40
    have h' : m > 40 := by omega
    have h3 : m ≤ 44 := by nlinarith [sq_nonneg (m : ℤ), sq_nonneg (n : ℤ), hsum]
    have h4 : n ≤ 19 := by nlinarith [sq_nonneg (m : ℤ), sq_nonneg (n : ℤ), hsum]
    interval_cases m <;> try { norm_num at hsum <;> try { 
      have : n ≤ 19 := by nlinarith
      interval_cases n <;> omega
    }
  }