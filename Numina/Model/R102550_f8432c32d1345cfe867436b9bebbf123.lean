import Mathlib

theorem algebra_217251 {a : ℕ → ℝ} (ha0 : a 0 = 11) (ha1 : a 1 = 11)
    (han : ∀ m n, a (m + n) = (a (2 * m) + a (2 * n)) / 2 - (m - n) ^ 2) :
    a 45 = 1991 := by

  have h1 : ∀ m, a (2 * m) = 2 * a m - 11 + 2 * (m : ℝ) ^ 2 := by
    intro m
    specialize han m 0
    simp at han
    linarith [ha0]

  have h2 : ∀ n, a n = 11 + (n : ℝ) * ((n : ℝ) - 1) := by
    intro n
    induction n with
    | zero =>
      simp [ha0]
      all_goals norm_num
    | succ n ih =>
      have eq1 := han n 1
      simp at eq1
      have h2n := h1 n
      have ha2 : a 2 = 13 := by
        specialize h1 1
        norm_num [ha1] at h1 ⊢
        linarith
      rw [show (n + 1 : ℕ) = n + 1 by omega] at *
      rw [ha2] at eq1
      rw [h2n] at eq1
      rw [ih] at eq1
      simp [add_assoc] at eq1 ⊢
      ring_nf at eq1 ⊢
      nlinarith

  have h45 := h2 45
  norm_num at h45 ⊢
  linarith