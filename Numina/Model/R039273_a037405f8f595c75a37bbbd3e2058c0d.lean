import Mathlib

open Real

theorem algebra_305976 (x : ℕ → ℝ)
    (hx1 : x 1 = 2 / 3)
    (hxn : ∀ n > 0, x (n + 1) = x n / (2 * (2 * n + 1) * x n + 1)) :
    ∑ i in Finset.Icc 1 2014, x i = 4028 / 4029 := by

  have h1 : ∀ n, x (n + 1) = 2 / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) := by
    intro n
    induction n with
    | zero =>
      rw [hx1]
      norm_num
    | succ n ih =>
      have eq1 : x (n + 2) = x (n + 1) / (2 * (2 * (n + 1 : ℕ) + 1) * x (n + 1) + 1) := by
        specialize hxn (n + 1) (by linarith)
        simpa using hxn
      rw [eq1]
      rw [ih]
      field_simp
      ring_nf

  have h2 : ∀ (n : ℕ), ∑ i in Finset.Icc 1 n, x i = 1 - 1 / (2 * (n : ℝ) + 1) := by
    intro n
    induction n with
    | zero =>
      norm_num [Finset.sum_eq_zero]
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      have eq1 : x (n + 1) = 2 / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) := by
        specialize h1 n
        simpa using h1
      rw [eq1]
      field_simp
      ring_nf

  specialize h2 2014
  norm_num at h2 ⊢
  <;> linarith