import Mathlib

theorem algebra_304111 {a : ℕ → ℝ} (P : ℝ → ℝ)
    (hP : ∀ x, P x = x^5 + a 1 * x^4 + a 2 * x^3 + a 3 * x^2 + a 4 * x + a 5)
    (hP1 : P 1 = 1997) (hP2 : P 2 = 2 * 1997) (hP3 : P 3 = 3 * 1997) (hP4 : P 4 = 4 * 1997) :
    P 10 - P (-5) = 75315 := by
  have eq1 := hP 1
  have eq2 := hP 2
  have eq3 := hP 3
  have eq4 := hP 4
  
  rw [eq1] at hP1
  rw [eq2] at hP2
  rw [eq3] at hP3
  rw [eq4] at hP4
  
  have eq10 := hP 10
  have eqm5 := hP (-5)
  
  rw [eq10, eqm5]
  linarith