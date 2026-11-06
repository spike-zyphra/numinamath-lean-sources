import Mathlib

theorem algebra_292841 {a b c : ℤ} (ha : 0 < a) (hroots : ∃ x y, x ∈ Set.Ioo 0 1 ∧ y ∈ Set.Ioo 0 1 ∧ a * x^2 + b * x + c = 0 ∧ a * y^2 + b * y + c = 0 ∧ x ≠ y) :
    a ≥ 5 := by 
  rcases hroots with ⟨x, y, hx, hy, hfx, hfy, hxy⟩
  have h1 : x > 0 := hx.left
  have h2 : x < 1 := hx.right
  omega