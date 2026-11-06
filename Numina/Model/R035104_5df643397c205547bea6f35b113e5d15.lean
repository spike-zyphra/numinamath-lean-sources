import Mathlib

theorem algebra_124317 {a b c : ℤ} (ha : a > 0) (hroots : ∃ x y, x ∈ Set.Ioo 0 1 ∧ y ∈ Set.Ioo 0 1 ∧ x ≠ y ∧ a * x ^ 2 + b * x + c = 0 ∧ a * y ^ 2 + b * y + c = 0) :
    a ≥ 5 := by
  rcases hroots with ⟨x, y, hx, hy, hxy, heq1, heq2⟩
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  omega