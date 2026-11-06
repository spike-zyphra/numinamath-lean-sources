import Mathlib

theorem algebra_278457 (a b c : ℤ) (ha : 0 < a) (hroots : ∃ x y, x ≠ y ∧ x ∈ Set.Ioo 0 1 ∧ y ∈ Set.Ioo 0 1 ∧
    a * x ^ 2 + b * x + c = 0 ∧ a * y ^ 2 + b * y + c = 0) :
    5 ≤ a := by 
  rcases hroots with ⟨x, y, hxy, hx, hy, hx2, hy2⟩
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  omega