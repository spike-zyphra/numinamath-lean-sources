import Mathlib

theorem algebra_190511 {a : ℕ → ℤ} (ha0 : a 0 = 2) (han : ∀ n ≥ 1, a n = a (n - 1) - n + 3) :
    ∀ n, a n = -n * (n + 1) / 2 + 3 * n + 2 := by 
  intro n 
  induction n with 
  | zero =>
    simp [ha0]
  | succ k ih =>
    have h1 : a (k + 1) = a k - ((k + 1 : ℕ) : ℤ) + 3 := by 
      specialize han (k + 1) (by linarith)
      simpa using han
    rw [h1]
    simp [ih]
    <;> ring_nf <;> omega