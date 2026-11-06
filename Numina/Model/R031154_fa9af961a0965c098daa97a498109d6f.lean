import Mathlib

theorem algebra_325705 (S : Finset ℚ) (hS : S.card = 100)
    (hS1 : ∀ x ∈ S, ∃ n, x = 1 / (n + 1)) :
    S.card = 1 → ∃ x ∈ S, x = 100 := by
  intro h
  have h1 : S.card = 100 := hS
  have h2 : S.card = 1 := h
  omega