import Mathlib

theorem algebra_95209_nat (a : ℝ → ℕ → ℝ) (h_pos : ∀ x n, 0 < a x n)
    (ha0 : ∀ x, a x 0 = x) (ha1 : ∀ x, a x 1 = 2000)
    (ha : ∀ x n, a x (n + 1) = a x n * a x (n + 2) - 1) :
    ∃ s : Finset ℝ, {x > 0 | 2001 ∈ Set.range (a x)} = s ∧ s.card = 4 := by

  have h1 := h_pos 0 0
  have h3 : a 0 0 = (0 : ℝ) := by
    specialize ha0 0
    linarith
  linarith [h3, h1]