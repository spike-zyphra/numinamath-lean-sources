import Mathlib

open Finset Real

theorem algebra_100265 {a : ℕ → ℝ}
    (ha : ∀ n, a n = (n * 11 + 1) / 11 - (n * 19 + 1) / 19) :
    ∃ m : ℕ, ∑ i ∈ range 209, a i = m := by
  have h1 : ∀ n, a n = (8 / 209 : ℝ) := by
    intro n
    rw [ha n]
    field_simp
    <;> ring_nf
    <;> norm_num
    all_goals linarith
  use 8
  have h2 : ∑ i ∈ range 209, a i = (8 : ℝ) := by
    norm_num [Finset.sum_range_succ, h1]
    all_goals norm_num
  exact_mod_cast h2
  all_goals norm_num