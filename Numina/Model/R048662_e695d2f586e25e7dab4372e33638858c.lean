import Mathlib

theorem algebra_113951 (a : ℕ → ℤ) (ha0 : a 0 = 1) (han : ∀ n, a (n + 1) = 2 * a n + n) :
    ∀ n, a n = 2 ^ (n + 1) - n - 1 := by 
  intro n 
  induction n with
  | zero =>
    simp [ha0]
  | succ n ih =>
    have h1 : a (n + 1) = 2 * a n + n := han n 
    rw [h1]
    rw [ih]
    simp [pow_succ]
    <;> ring_nf
    <;> omega