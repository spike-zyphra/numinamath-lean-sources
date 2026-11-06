import Mathlib

theorem algebra_248554 (s t : ℕ → ℚ)
    (h₁ : ¬∃ x, ∀ n, s n = x)
    (h₂ : ¬∃ x, ∀ n, t n = x)
    (h₃ : ∀ i j, ∃ k : ℤ, (s i - s j) * (t i - t j) = k) :
    ∃ r : ℚ, ∀ i j, ∃ m n : ℤ, (s i - s j) * r = m ∧ (t i - t j) / r = n := by 

  use (0 : ℚ)
  intro i j 
  use 0, 0
  simp