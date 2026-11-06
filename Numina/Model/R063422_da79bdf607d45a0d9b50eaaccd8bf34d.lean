import Mathlib

open scoped BigOperators

theorem algebra_187387 {a : ℕ → ℝ}
  (ha1 : a 1 = 1)
  (han : ∀ n ≥ 1, a (n + 1) = a n + 2 * a n / n) :
  a 999 = 499500 := by

  have h1 : ∀ (n : ℕ), a (n + 1) = ((↑n + 1 : ℝ) * (↑n + 2 : ℝ)) / 2 := by
    intro n
    induction n with
    | zero =>
      norm_num at ha1 ⊢
      linarith
    | succ n ih =>
      have eq1 : a ((n + 1) + 1) = a (n + 1) + 2 * a (n + 1) / (↑n + 1 : ℝ) := by
        specialize han (n + 1) (by omega)
        simpa using han
      rw [eq1]
      rw [ih]
      field_simp
      ring
      <;> norm_num
      <;> linarith

  have h2 := h1 998
  norm_num at h2 ⊢
  linarith