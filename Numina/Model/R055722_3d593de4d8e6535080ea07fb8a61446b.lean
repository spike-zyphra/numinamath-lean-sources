import Mathlib

theorem algebra_135679 (a : ℕ → ℝ) (ha : ∀ n, ∃ x y, x ≠ y ∧ x^2 + a n * x + a (n + 1) = 0 ∧ y^2 + a n * y + a (n + 1) = 0)
    (ha' : ∀ n, a n > 0) :
    ¬∃ n, a n = 0 := by 
  intro h
  rcases h with ⟨n, hn⟩
  have h1 : a n > 0 := ha' n
  linarith