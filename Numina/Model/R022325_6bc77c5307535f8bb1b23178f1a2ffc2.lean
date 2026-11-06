import Mathlib

theorem algebra_138558 (a b c : ℤ) (ha : 0 < a) (hroots : ∃ x y, x ≠ y ∧ x ∈ Set.Ioo 0 1 ∧ y ∈ Set.Ioo 0 1 ∧
    a * x ^ 2 - b * x + c = 0 ∧ a * y ^ 2 - b * y + c = 0) :
    a ≥ 5 := by
  rcases hroots with ⟨x, y, hxy, hx, hy, heq1, heq2⟩
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  have h5 : x < 1 := hx1
  have h6 : x > 0 := hx0
  have h7 : x = 0 := by
    omega
  omega