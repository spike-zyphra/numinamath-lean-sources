import Mathlib

theorem algebra_94496 (a b c : ℤ) (ha : a ≠ 0) (h : a * 2 ^ 2 + b * 2 + c = 3844 ∧
    a * 3 ^ 2 + b * 3 + c = 3969 ∧ a * 4 ^ 2 + b * 4 + c = 4096 ∧
    a * 5 ^ 2 + b * 5 + c = 4227 ∧ a * 6 ^ 2 + b * 6 + c = 4356 ∧
    a * 7 ^ 2 + b * 7 + c = 4489 ∧ a * 8 ^ 2 + b * 8 + c = 4624 ∧
    a * 9 ^ 2 + b * 9 + c = 4761) : a * 5 ^ 2 + b * 5 + c ≠ 4227 := by 
  rcases h with ⟨h2, h3, h4, h5, h6, h7, h8, h9⟩
  omega