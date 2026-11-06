import Mathlib

theorem algebra_21017 {a : ℕ → ℝ} (ha0 : a 0 = 6)
    (han : ∀ n ≥ 1, a n = a (n - 1) / (1 + a (n - 1))) :
    a 100 = 6 / 601 := by

  have h1 : a 1 = 6 / 7 := by 
    specialize han 1 (by norm_num)
    rw [show (1 - 1 : ℕ) = 0 by omega] at han
    rw [ha0] at han
    norm_num at han ⊢
    linarith

  have h2 : ∀ n : ℕ, a (n + 1) = 6 / (6 * (n + 1) + 1) := by
    intro n
    induction n with
    | zero =>
      norm_num at *
      linarith [h1]
    | succ n ih =>
      have ha : a (n + 2) = a (n + 1) / (1 + a (n + 1)) := by
        specialize han (n + 2) (by omega)
        simpa using han
      rw [show (n + 2 : ℕ) = (n + 1) + 1 by rfl] -- trivial identity
      rw [ha]
      rw [ih]
      field_simp
      ring_nf
      <;> norm_num
      <;> ring

  have h100 := h2 99
  norm_num at h100 ⊢
  linarith