import Mathlib

open Finset Real

theorem algebra_148405 {n : ℕ} (hn : 2 ≤ n) :
    ∑ i ∈ Icc 1 (n - 1), (1 / (i * (i + 1) : ℝ)) = 1 - 1 / (n : ℝ) := by
  have h1 : n ≥ 2 := by linarith
  have h3 : ∀ (m : ℕ), ∑ i in Icc 1 (m), (1 / (i * (i + 1) : ℝ)) = 1 - 1 / ((m + 1 : ℝ)) := by
    intro m
    induction m with
    | zero =>
      norm_num
    | succ m ih =>
      rw [sum_Icc_succ_top (by linarith)]
      rw [ih]
      field_simp at *
      ring
  have h4 : ∑ i in Icc 1 (n - 1), (1 / (i * (i + 1) : ℝ)) = 1 - 1 / ((↑(n - 1) + 1 : ℝ)) := by
    specialize h3 (n - 1)
    simpa using h3
  rw [h4]
  have h5 : (↑(n - 1) + 1 : ℝ) = (↑n : ℝ) := by
    cases n with
    | zero => linarith
    | succ n =>
      simp at *
      all_goals norm_num
  rw [h5]
  all_goals norm_num