import Mathlib

open Finset Real

theorem algebra_308908 {u : ℕ → ℝ} (hu : ∀ k, u k = 1 / (k * (k + 1) * (k + 2) * (k + 3))) :
    ∑ k ∈ Icc 1 n, u k = (1 / 3) * (1 / 6 - 1 / ((n + 1) * (n + 2) * (n + 3))) := by 
  have h1 : ∀ k : ℕ, u k = 1 / (k * (k + 1) * (k + 2) * (k + 3)) := hu
  induction n with
  | zero =>
    simp [Finset.sum_eq_zero]
    <;> norm_num [h1] at *
  | succ n ih =>
    rw [sum_Icc_succ_top (by linarith)]
    rw [ih]
    simp [h1]
    all_goals
      field_simp
      ring_nf
      <;> field_simp <;> ring