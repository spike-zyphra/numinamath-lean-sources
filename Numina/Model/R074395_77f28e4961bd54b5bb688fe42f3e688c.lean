import Mathlib

theorem algebra_312839 (a : ℕ → ℤ) (ha1 : a 1 = 1) (han : ∀ n, a (n + 1) = 1 + 2 * a n) :
    ∀ n, a n = 2 ^ n - 1 := by
  intro n
  induction n with
  | zero =>
    have ha0 : a 0 = 0 := by
      specialize han 0
      norm_num at han
      rw [ha1] at han
      linarith
    simp [ha0]
  | succ n ih =>
    have h1 : a (n + 1) = 1 + 2 * a n := han n
    rw [h1]
    rw [ih]
    simp [pow_succ]
    <;> ring