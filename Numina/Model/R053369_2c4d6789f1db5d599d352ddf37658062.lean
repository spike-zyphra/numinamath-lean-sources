import Mathlib

theorem algebra_283848 (a : ℕ → ℝ) (ha1 : a 1 = 1 / 2)
    (han : ∀ n > 0, a (n + 1) = 2 * a n / (3 * a n + 2)) :
    a 2017 = 1 / 3026 := by
  have h1 : ∀ n, a (n + 1) = 2 / (3 * (n + 1 : ℝ) + 1) := by
    intro n
    induction n with
    | zero =>
      -- Base case n = 0: Show that a 1 = 2 / (3 * 1 + 1)
      rw [show (0 + 1 : ℕ) = 1 by omega]
      norm_num at ha1 ⊢
      linarith
    | succ n ih =>
      -- Inductive step: show that a (n + 2) = 2 / (3 * (n + 2) + 1)
      have h2 : (n + 2 : ℕ) = (n + 1) + 1 := by omega
      rw [h2]
      specialize han (n + 1) (by omega)
      rw [han]
      rw [ih]
      field_simp
      <;> ring_nf <;> linarith
  -- now use the formula to compute a 2017
  have h2017 := h1 2016
  norm_num at h2017 ⊢
  linarith