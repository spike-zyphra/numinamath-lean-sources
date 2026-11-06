import Mathlib

theorem algebra_163740 {x y : ℕ} (h : x + y = 240) (h' : x = 47 * y) :
    x = 235 ∧ y = 5 := by
  have eq1 : y = 5 := by
    omega
  have eq2 : x = 235 := by
    subst eq1
    omega
  exact ⟨eq2, eq1⟩