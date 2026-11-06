import Mathlib

open scoped BigOperators

theorem algebra_222561 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 2)
  (han : ∀ n, a (n + 1) = a n / (2 * a n + 1)) :
  a 1000 = 1 / 2000 := by

  have h1 : ∀ n, a (n + 1) = 1 / (2 * ((n : ℝ) + 1)) := by
    intro n
    induction n with
    | zero =>
      norm_num [ha1]
    | succ n ih =>
      have h2 : a (n + 2) = a (n + 1) / (2 * a (n + 1) + 1) := han (n + 1)
      rw [h2]
      simp [ih]
      <;> field_simp at *
      <;> ring_nf
      <;> field_simp at *
      <;> ring

  have h1000 := h1 999
  norm_num at h1000 ⊢
  linarith