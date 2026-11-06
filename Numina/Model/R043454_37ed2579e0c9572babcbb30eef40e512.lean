import Mathlib

theorem algebra_278690 (a n : ℕ) (ha : 0 < a) (hn : 0 < n) :
    ∑ i ∈ Finset.range n, (1 / ((a + i) * (a + i + 1)) : ℚ) = n / (a * (a + n)) := by
  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 / ((a + i) * (a + i + 1)) : ℚ) = n / (a * (a + n)) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp
      <;> ring
  specialize h1 n
  simpa using h1