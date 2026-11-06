import Mathlib

theorem algebra_163907 (r b y : ℕ) (h₀ : r + b + y = 18)
    (h₁ : b = 2 * r - 1) (h₂ : y = 3 * r + 1) :
    r = 3 ∧ b = 5 ∧ y = 10 := by
  have hr : r = 3 := by 
    omega 
  have hb : b = 5 := by 
    rw [hr] at h₁ 
    omega 
  have hy : y = 10 := by 
    rw [hr] at h₂ 
    omega 
  exact ⟨hr, hb, hy⟩