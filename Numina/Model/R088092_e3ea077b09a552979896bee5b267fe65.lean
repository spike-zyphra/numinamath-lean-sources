import Mathlib

theorem algebra_61375 {P : Polynomial ℤ} :
    ∃ Q R : Polynomial ℤ, (∃ h : Polynomial ℤ, P * Q = h.comp (X ^ 2)) ∧
    (∃ h : Polynomial ℤ, P * R = h.comp (X ^ 3)) := by 
  use 0
  use 0
  constructor
  · -- Show that there exists h such that P * 0 = h.comp (X ^ 2)
    use 0
    simp -- simplifies P * 0 = 0 with simp
  · -- Show that there exists h such that P * 0 = h.comp (X ^ 3)
    use 0
    simp -- simplifies P * 0 = 0 with simp