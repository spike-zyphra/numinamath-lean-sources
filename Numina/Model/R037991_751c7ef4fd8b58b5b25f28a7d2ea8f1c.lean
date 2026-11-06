import Mathlib

theorem algebra_119132 {a b : ℤ} (h₀ : ∃ m n : ℤ, a + b = m ∧ a * b / (a + b) = n) :
    ∃ p : ℤ, (a ^ 2 + b ^ 2) / (a + b) = p := by 
  refine' ⟨(a ^ 2 + b ^ 2) / (a + b), rfl⟩