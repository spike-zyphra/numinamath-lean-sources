import Mathlib

theorem algebra_159683 {a b : ℕ → ℤ}
    (ha0 : a 0 = 1) (ha1 : a 1 = 1)
    (han : ∀ n, a (n + 1) = a n + 2 * a (n - 1))
    (hb0 : b 0 = 1) (hb1 : b 1 = 7)
    (hbn : ∀ n, b (n + 1) = 2 * b n + 3 * b (n - 1)) :
    ∀ n, a n = b n → n = 0 ∨ a n = 1 ∨ b n = 1 := by

  intro n h
  have ha2 := han 0
  have ha3 : a 1 = 3 := by
    rw [show (0 : ℕ) - 1 = 0 by omega] at ha2
    simp [ha0] at ha2
    nlinarith
  have ha4 : a 1 = 1 := ha1
  omega