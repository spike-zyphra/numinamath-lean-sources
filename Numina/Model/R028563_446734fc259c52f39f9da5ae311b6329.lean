import Mathlib

theorem algebra_100337 (k p q : ℕ) (hp : p > 0) (hq : q > 0)
    (hroots : ∃ x y, x ≠ y ∧ x ∈ Set.Ioo 0 1 ∧ y ∈ Set.Ioo 0 1 ∧
      k * x ^ 2 - p * x + q = 0 ∧ k * y ^ 2 - p * y + q = 0) :
    k ≥ 5 := by
  rcases hroots with ⟨x, y, h_neq, hx, hy, hkx, hky⟩
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  have h1 : x > 0 := by
    linarith
  have h2 : x < 1 := by
    linarith
  omega