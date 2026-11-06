import Mathlib

theorem number_theory_222881 {n p : ℕ} (hn : n > 0) (hp : p > 0)
    (h : ∀ i j, i * j + (i + j) = p → i = n ∧ j = n) :
    Nat.Prime (n + 1) := by
  have h1 := h 0 p (by linarith)
  have h2 : n = 0 := by linarith [h1.1]
  linarith