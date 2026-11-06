import Mathlib

open Finset Real

theorem algebra_278665 {n : ℕ} :
    ∑ i ∈ Icc 1 n, (1 / (i * (i + 1) * (i + 2))) =
    ((1 / 2) * (1 / 2 - 1 / ((n + 1) * (n + 2)))) := by
  induction n with
  | zero =>
    simp
    <;> norm_num
  | succ k ih =>
    rw [sum_Icc_succ_top (by omega)]
    rw [ih]
    field_simp
    ring_nf
    <;> norm_num
    <;> ring_nf
    <;> omega