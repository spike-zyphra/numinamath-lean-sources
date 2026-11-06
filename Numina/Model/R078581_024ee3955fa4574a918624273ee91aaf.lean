import Mathlib

theorem number_theory_310826 (a : ℕ → ℕ) (ha : ∀ k, 0 < a k)
    (hinc : ∀ k, a k < a (k + 1)) :
    ∀ n, ∃ m, m > n ∧ ∃ p q x y, a m = x * a p + y * a q ∧ p ≠ q := by 
  intro n
  use (n + 1)
  constructor
  . -- Show that $n + 1 > n$
    omega
  . -- Show the existence of p, q, x, y
    use (n + 1), 0, 1, 0
    constructor
    . -- Show that $a (n + 1) = 1 * a (n + 1) + 0 * a 0$
      simp
    . -- Show that $n + 1 \neq 0$
      omega