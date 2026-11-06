import Mathlib


theorem Algebra_604504 {a b : ℕ → ℤ} (ha₀ : a 0 = 0) (hb₀ : b 0 = 8) (ha : ∀ (n : ℕ), a (n + 2) = 2 * a (n + 1) - a n + 2)
  (hb : ∀ n, b (n + 2) = 2 * b (n + 1) - b n) : 
  ∃ (A B A' B': ℤ), (A ≠ A') ∧ ((((a 1 = A + 1) ∧ (b 1 = B + 8)) → (∀ (n : ℕ), ∃ (k : ℤ), ((a n) ^ 2 + (b n) ^ 2 = k ^ 2)) ) 
  ∧  (((a 1 = A' + 1) ∧ (b 1 = B' + 8)) → (∀ (n : ℕ), ∃ (k : ℤ), ((a n) ^ 2 + (b n) ^ 2 = k ^ 2)))) := by

  use (a 1), (b 1 - 8), (a 1 + 1), (b 1 - 8)
  constructor
  · -- Show that A ≠ A'
    omega
  constructor
  · -- First implication
    intro h
    exfalso
    omega
  · -- Second implication
    intro h
    exfalso
    omega