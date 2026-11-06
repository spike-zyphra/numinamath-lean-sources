import Mathlib

theorem number_theory_77120 (a b c : ℤ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : ¬∃ x y z : ℤ, x * a + y * b + z * c = 0) :
    ∃ x y z : ℤ, a * b * c = x^2 + y^2 + z^2 := by 
  have h2 : ∃ x y z : ℤ, x * a + y * b + z * c = 0 := by 
    use 0, 0, 0 
    all_goals simp
  contradiction