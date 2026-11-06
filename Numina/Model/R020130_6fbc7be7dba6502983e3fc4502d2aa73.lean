import Mathlib

theorem algebra_314933 (a : ℕ → ℝ) (ha1 : a 1 = 1 / 2)
    (han : ∀ n > 0, a (n + 1) = 2 * a n / (3 * a n + 2)) :
    a 2017 = 1 / 3026 := by

  have h1 : ∀ (n : ℕ), a (n + 1) = 2 / (3 * (n) + 4) := by
    intro n
    induction n with
    | zero =>
      norm_num [ha1]
    | succ n ih =>
      have h2 := han (n + 1) (by omega)
      simp [show n + 1 + 1 = n + 2 by omega] at h2 ⊢
      rw [h2]
      rw [ih]
      field_simp
      ring_nf

  have h2017 := h1 2016
  norm_num at h2017 ⊢
  linarith