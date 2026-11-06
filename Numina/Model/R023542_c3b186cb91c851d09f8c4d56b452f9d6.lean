import Mathlib

theorem algebra_201596 (n : ℕ) (h₀ : n > 0) (h₁ : ∃ k : ℕ, (47 / 5 : ℚ) * (4 / 47 + n / 141) = k) :
    n % 15 = 3 := by

  rcases h₁ with ⟨k, hk⟩

  have eq1 : (47 / 5 : ℚ) * (4 / 47 + (n : ℚ) / 141) = (12 + (n : ℚ)) / 15 := by
    field_simp
    <;> ring

  rw [eq1] at hk

  have h2 : (12 + (n : ℚ)) = (15 * (k : ℚ)) := by 
    field_simp at hk ⊢
    linarith

  have eq4 : (12 + n) = 15 * k := by
    exact_mod_cast h2

  omega