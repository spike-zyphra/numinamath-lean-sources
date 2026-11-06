import Mathlib

theorem algebra_297702 (p q r s : ℝ) (h₀ : p + q + r + s = 9) (h₁ : p^2 + q^2 + r^2 + s^2 = 21) :
    ∃ a b c d, a = p ∧ b = q ∧ c = r ∧ d = s ∨ a = p ∧ b = q ∧ c = s ∧ d = r ∨
    a = p ∧ b = r ∧ c = q ∧ d = s ∨ a = p ∧ b = r ∧ c = s ∧ d = q ∨
    a = p ∧ b = s ∧ c = q ∧ d = r ∨ a = p ∧ b = s ∧ c = r ∧ d = q ∨
    a = q ∧ b = p ∧ c = r ∧ d = s ∨ a = q ∧ b = p ∧ c = s ∧ d = r ∨
    a = q ∧ b = r ∧ c = p ∧ d = s ∨ a = q ∧ b = r ∧ c = s ∧ d = p ∨
    a = q ∧ b = s ∧ c = p ∧ d = r ∨ a = q ∧ b = s ∧ c = r ∧ d = p ∨
    a = r ∧ b = p ∧ c = q ∧ d = s ∨ a = r ∧ b = p ∧ c = s ∧ d = q ∨
    a = r ∧ b = q ∧ c = p ∧ d = s ∨ a = r ∧ b = q ∧ c = s ∧ d = p ∨
    a = r ∧ b = s ∧ c = p ∧ d = q ∨ a = r ∧ b = s ∧ c = q ∧ d = p ∨
    a = s ∧ b = p ∧ c = q ∧ d = r ∨ a = s ∧ b = p ∧ c = r ∧ d = q ∨
    a = s ∧ b = q ∧ c = p ∧ d = r ∨ a = s ∧ b = q ∧ c = r ∧ d = p ∧ a * b - c * d ≥ 2 := by 
  refine' ⟨p, q, r, s, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩ 
  all_goals nlinarith