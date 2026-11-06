import Mathlib

theorem algebra_195825 (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (2002 : ℝ)^i = (2002^(n + 1) - 1) / 2001 := by
  have h1 : ∀ (n : ℕ), ∑ i in Finset.range (n + 1), (2002 : ℝ) ^ i = (2002 ^ (n + 1) - 1) / 2001 := by
    intro n 
    induction n with
    | zero =>
      norm_num [Finset.sum_range_succ]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp
      ring_nf
  specialize h1 n
  simpa using h1