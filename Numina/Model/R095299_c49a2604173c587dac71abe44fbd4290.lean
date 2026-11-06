import Mathlib

theorem algebra_187370 (a : ℕ → ℝ) (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, a (n + 1) = a n + 2 * a n / n) :
    a 200 = 20100 := by

  have h1 : ∀ n : ℕ, a (n + 1) = (n + 1 : ℝ) * (n + 2 : ℝ) / 2 := by
    intro n
    induction n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n ih =>
      have h1 := han (n + 1) (by linarith)
      rw [show n + 1 + 1 = n + 2 by omega] at h1
      rw [h1]
      rw [ih]
      field_simp
      ring
      all_goals norm_num
      all_goals linarith
  have h200 := h1 199
  norm_num at h200 ⊢
  exact h200