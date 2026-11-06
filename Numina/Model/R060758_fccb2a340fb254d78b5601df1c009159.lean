import Mathlib

theorem algebra_62425 {p : ℕ → ℕ → ℕ} (hp : ∀ m n, p m n = m^2 + n * (m - 1)) :
    ∀ m n, p m n = m^2 + n * (m - 1) := by
  intro m n
  exact hp m n