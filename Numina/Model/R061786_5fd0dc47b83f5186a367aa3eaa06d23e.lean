import Mathlib

theorem number_theory_256773 {a b c : ℤ} (h : ∃ k : ℤ, a * b / c + a * c / b + b * c / a = k) :
    ∃ m n p : ℤ, a * b / c = m ∧ a * c / b = n ∧ b * c / a = p := by
  refine' ⟨a * b / c, a * c / b, b * c / a, rfl, rfl, rfl⟩