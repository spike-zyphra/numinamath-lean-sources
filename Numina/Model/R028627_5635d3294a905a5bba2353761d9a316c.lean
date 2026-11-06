import Mathlib

theorem algebra_304111 {a : ℕ → ℝ} (P : ℝ → ℝ)
    (hP : ∀ x, P x = x^5 + a 1 * x^4 + a 2 * x^3 + a 3 * x^2 + a 4 * x + a 5)
    (hP1 : P 1 = 1997) (hP2 : P 2 = 2 * 1997) (hP3 : P 3 = 3 * 1997) (hP4 : P 4 = 4 * 1997) :
    P 10 - P (-5) = 75315 := by
  have eq1 : 1^5 + a 1 * 1^4 + a 2 * 1^3 + a 3 * 1^2 + a 4 * 1 + a 5 = 1997 := by
    rw [hP 1] at hP1
    linarith
  have eq2 : 2^5 + a 1 * 2^4 + a 2 * 2^3 + a 3 * 2^2 + a 4 * 2 + a 5 = 2 * 1997 := by
    rw [hP 2] at hP2
    linarith
  have eq3 : 3^5 + a 1 * 3^4 + a 2 * 3^3 + a 3 * 3^2 + a 4 * 3 + a 5 = 3 * 1997 := by
    rw [hP 3] at hP3
    linarith
  have eq4 : 4^5 + a 1 * 4^4 + a 2 * 4^3 + a 3 * 4^2 + a 4 * 4 + a 5 = 4 * 1997 := by
    rw [hP 4] at hP4
    linarith
  have eq5 : P 10 = 10^5 + a 1 * 10^4 + a 2 * 10^3 + a 3 * 10^2 + a 4 * 10 + a 5 := by
    apply hP
  have eq6 : P (-5) = (-5)^5 + a 1 * (-5)^4 + a 2 * (-5)^3 + a 3 * (-5)^2 + a 4 * (-5) + a 5 := by
    apply hP
  rw [eq5, eq6]
  linarith [eq1, eq2, eq3, eq4]