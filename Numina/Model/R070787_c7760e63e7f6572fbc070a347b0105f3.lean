import Mathlib

theorem algebra_280229 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (h : ∀ i, a i = d i) :
    ∃ c, ∀ p : Equiv.Perm (Fin n), c = ∑ i, a i * d i := by

  use ∑ i, a i * d i

  intro p

  rfl