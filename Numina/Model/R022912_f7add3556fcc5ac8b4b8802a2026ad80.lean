import Mathlib

theorem number_theory_239198 (n : ℕ) (h : n > 0) (a b : ℕ)
    (ha : a = ∑ i ∈ Finset.range n, (2 * i + 1)) (hb : b = ∑ i ∈ Finset.range n, (2 * i + 2))
    (h1 : a + b = n) (h2 : a = 101) :
    n = 211 := by 
  have h3 : a = n ^ 2 := by
    rw [ha]
    have h4 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ]
        rw [ih]
        all_goals
          ring_nf
          <;> omega
    specialize h4 n
    simpa using h4
  have h4 : b = n * (n + 1) := by
    rw [hb]
    have h5 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (2 * i + 2) = n * (n + 1) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ]
        rw [ih]
        all_goals
          ring_nf
          <;> omega
    specialize h5 n
    simpa using h5
  rw [h3] at h2
  rw [h3, h4] at h1
  nlinarith