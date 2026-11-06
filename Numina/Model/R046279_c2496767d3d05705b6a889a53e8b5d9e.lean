import Mathlib

def is_interesting (n : ℕ) := ∃ x y : ℤ , n = x^2 + 2 * y^2

theorem number_theory_169848 {m n : ℕ} (hm : is_interesting m) (hn : is_interesting n) :
    ∃ x y : ℤ , m * n = x^2 + 2 * y^2 := by
  rcases hm with ⟨x₁, y₁, hm_eq⟩ 
  rcases hn with ⟨x₂, y₂, hn_eq⟩
  use (x₁ * x₂ - 2 * y₁ * y₂)
  use (x₁ * y₂ + y₁ * x₂)
  have eq1 : (m : ℤ) = x₁^2 + 2 * y₁^2 := by
    exact_mod_cast hm_eq
  have eq2 : (n : ℤ) = x₂^2 + 2 * y₂^2 := by
    exact_mod_cast hn_eq
  have eq3 : (m * n : ℤ) = (x₁^2 + 2 * y₁^2) * (x₂^2 + 2 * y₂^2) := by
    rw [eq1, eq2]
    <;> ring
  have eq4 : (x₁^2 + 2 * y₁^2) * (x₂^2 + 2 * y₂^2) =
      (x₁ * x₂ - 2 * y₁ * y₂) ^2 + 2 * (x₁ * y₂ + y₁ * x₂)^2 := by
    ring
  have eq5 : (m * n : ℤ) = (x₁ * x₂ - 2 * y₁ * y₂) ^2 + 2 * (x₁ * y₂ + y₁ * x₂)^2 := by
    rw [eq3, eq4]
  exact_mod_cast eq5