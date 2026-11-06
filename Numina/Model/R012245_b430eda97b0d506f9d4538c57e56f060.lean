import Mathlib

open Finset

theorem number_theory_192221  :
  ∃ k, ∃ m ,  ∑ i ∈ Finset.range 100, (2 : ℝ) ^ (k + i) = ∑ i ∈ Finset.range m, ((i : ℝ) + 1):= by
  use 99
  use (2 ^ 100 - 1 : ℕ)
  have h1 : ∑ i in range 100, (2 : ℝ) ^ (99 + i : ℕ) = (2 ^ 99 * (2 ^ 100 - 1) : ℝ) := by
    norm_num [Finset.sum_range_succ, pow_add, mul_add]
    <;> ring_nf
  have h2 : ∑ i in range ((2 ^ 100 - 1 : ℕ)), ((i : ℝ) + 1) = ((2 ^ 100 - 1 : ℝ) * (2 ^ 100 : ℝ) / 2 : ℝ) := by
    have h3 : ∀ n : ℕ, ∑ i in range n, ((i : ℝ) + 1) = ((n : ℝ) * ((n : ℝ) + 1) / 2 : ℝ) := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp at *
        ring_nf
    specialize h3 (2 ^ 100 - 1 : ℕ)
    rw [h3]
    all_goals
      ring_nf
  rw [h1, h2]
  norm_num