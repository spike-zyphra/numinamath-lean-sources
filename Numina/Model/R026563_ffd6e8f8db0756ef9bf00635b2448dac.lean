import Mathlib

open scoped BigOperators

theorem algebra_59009
  (a : ℕ → ℝ)
  (h₀ : a 1 = 1)
  (h₁ : ∀ n ≥ 1, 3 * a (n + 1) - 3 * a n = 1) :
  a 2002 = 668 := by

  have h2 : ∀ n : ℕ, a (n + 1) = 1 + (n / 3 : ℝ) := by
    intro n
    induction n with
    | zero =>
      norm_num [h₀]
    | succ n ih =>
      have eq1 : 3 * a (n + 2) - 3 * a (n + 1) = 1 := by
        specialize h₁ (n + 1) (by linarith)
        simpa using h₁
      have eq2 : a (n + 1) = 1 + (n / 3 : ℝ) := by
        simpa using ih
      have eq3 : a (n + 2) = a (n + 1) + (1 / 3 : ℝ) := by 
        linarith
      rw [eq3, eq2]
      field_simp at *
      <;> ring_nf
  have h3 : a 2002 = 1 + (2001 / 3 : ℝ) := by
    specialize h2 2001
    norm_num at h2 ⊢
    linarith
  rw [h3]
  norm_num