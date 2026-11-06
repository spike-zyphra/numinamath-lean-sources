import Mathlib

theorem number_theory_100796 (a : ℕ → ℕ) (ha : ∀ k, a k < a (k + 1))
    (ha' : ∀ k, 0 < a k) :
    ∀ n, ∃ m, m > n ∧ ∃ p q x y, a m = x * a p + y * a q ∧ p ≠ q := by
  intro n
  use n + 1
  constructor
  · -- Show that n + 1 > n
    omega
  · -- Show the existence of p, q, x, y such that a (n + 1) = x * a p + y * a q ∧ p ≠ q
    use n + 1, n, 1, 0
    all_goals
      try { 
        simp [mul_add, add_mul] at *
        all_goals tauto 
      }
      all_goals omega