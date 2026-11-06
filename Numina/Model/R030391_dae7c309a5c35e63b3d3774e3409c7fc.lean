import Mathlib

theorem number_theory_209016 (f : ℕ → ℕ)
  (h₀ : ∀ x, 0 < x → 0 < f x)
  (h₁ : ∀ a b, ∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧
    x + y > z ∧ y + z > x ∧ z + x > y ∧
    x = a ∧ y = f b ∧ z = f (b + f a - 1)) :
  (∀ x, 0 < x → f x = x) := by
  have h2 := h₁ 0 0
  rcases h2 with ⟨x, y, z, hx1, hy1, hz1, h1, h2, h3, heq1, heq2, heq3⟩
  all_goals
    omega