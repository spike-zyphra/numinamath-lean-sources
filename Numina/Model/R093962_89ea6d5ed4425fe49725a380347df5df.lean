import Mathlib

theorem algebra_607838 {P : Polynomial ℤ} :
    ∃ Q R : Polynomial ℤ, (∃ p : Polynomial ℤ, P * Q = p.comp (Polynomial.X^2)) ∧ (∃ p : Polynomial ℤ, P * R = p.comp (Polynomial.X^3)) := by 
  use 0, 0
  constructor
  · -- Show that there exists a polynomial p such that P * 0 = p.comp (Polynomial.X^2)
    use 0
    all_goals simp
  · -- Show that there exists a polynomial p such that P * 0 = p.comp (Polynomial.X^3)
    use 0
    all_goals simp