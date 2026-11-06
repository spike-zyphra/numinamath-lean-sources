import Mathlib

open Finset Real

theorem algebra_10278 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 3)
    (han : ∀ n ≥ 1, a (n + 1) = a n / (2 - (2 * n + 1) * (2 * n - 5) * a n)) :
    ∑ i ∈ range 2023, a (i + 1) = 2023 / 4047 := by

  have h1 : ∀ n : ℕ, a (n + 1) = 1 / (4 * ((n + 1 : ℝ) ) ^ 2 - 1) := by
    intro n
    induction n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n ih =>
      have eq2 := han (n + 1) (by linarith)
      rw [show n + 1 + 1 = n + 2 by omega] at eq2
      rw [eq2, ih]
      field_simp [show 4 * ((n + 1 : ℝ) ) ^ 2 - 1 ≠ 0 by
        have h3 : 4 * ((n + 1 : ℝ) ) ^ 2 - 1 > 0 := by
          have h3 : (n : ℝ) ≥ 0 := by
            exact_mod_cast show (0 : ℝ) ≤ (n : ℝ) by linarith [show (n : ℝ) ≥ 0 by positivity]
          nlinarith [sq_nonneg ((n : ℝ) ), sq_nonneg ((n + 1 : ℝ) ) ]
        nlinarith
      ]
      ring_nf

  have h2 : ∀ (N : ℕ), ∑ i ∈ range N, a (i + 1) = (N : ℝ) / (2 * (N : ℝ) + 1) := by
    intro N
    induction N with
    | zero =>
      simp
    | succ N ih =>
      rw [sum_range_succ, ih]
      rw [h1 N]
      field_simp [show 4 * ((N + 1 : ℝ) ) ^ 2 - 1 ≠ 0 by
        have h3 : 4 * ((N + 1 : ℝ) ) ^ 2 - 1 > 0 := by
          have h3 : (N : ℝ) ≥ 0 := by
            exact_mod_cast show (0 : ℝ) ≤ (N : ℝ) by linarith [show (N : ℝ) ≥ 0 by positivity]
          nlinarith [sq_nonneg ((N : ℝ) ), sq_nonneg ((N + 1 : ℝ) ) ]
        nlinarith
      ]
      ring_nf

  specialize h2 2023
  norm_num at h2 ⊢
  linarith