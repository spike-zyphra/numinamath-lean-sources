import Mathlib

open Real

theorem algebra_3762: ∑ i ∈ Finset.range 1017, (1 / ((i + 1001) * (i + 1002) : ℝ)) = 1017 / 2020018 := by
  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 / ((i + 1001) * (i + 1002) : ℝ)) = (n : ℝ) / ( (1001 : ℝ) * ( (1001 : ℝ) + (n : ℝ) ) ) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp at *
      ring_nf
      <;> norm_num
      <;> ring
  rw [h1 1017]
  norm_num
  <;> ring_nf <;> norm_num