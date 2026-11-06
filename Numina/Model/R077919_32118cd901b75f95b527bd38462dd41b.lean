import Mathlib

theorem algebra_278485 (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) / 2 := by
  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) / 2 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      ring_nf
      <;> omega
  specialize h1 n
  simpa using h1