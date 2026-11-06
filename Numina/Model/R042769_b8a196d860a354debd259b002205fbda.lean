import Mathlib

theorem algebra_3698 {A B C D E F G H : ℤ}
  (h : ∀ x y, (x - y + A) * (x + y + B) = C * x ^ 2 + D * x * y + E * y ^ 2 + F * x + G * y + H) :
  C - E - D * A * B = 2 := by
  have eq1 := h 0 0
  have eq2 := h 1 0
  have eq3 := h 0 1
  have eq4 := h 1 1
  have eq5 := h 1 (-1)
  have eq6 := h 2 1
  have eq7 := h 1 2
  simp at eq1 eq2 eq3 eq4 eq5 eq6 eq7
  have hC : C = 1 := by
    nlinarith [eq1, eq2, eq3, eq4, eq5, eq6, eq7]
  have hE : E = -1 := by
    nlinarith [eq1, eq2, eq3, eq4, eq5, eq6, eq7]
  have hD : D = 0 := by
    nlinarith [eq1, eq2, eq3, eq4, eq5, eq6, eq7]
  rw [show C = 1 by linarith, show E = -1 by linarith, show D = (0 : ℤ) by linarith]
  all_goals
    ring