import Mathlib

theorem algebra_141308 {a r : ℚ} (hr : r > 0) (h : a + ar + ar^2 = 13 ∧ ar^2 + ar^3 + ar^4 = 39 ∧ ar^4 + ar^5 + ar^6 = 27) :
    a = 1 ∧ r = 2 ∧ a + ar + ar^2 = 13 ∧ ar^2 + ar^3 + ar^4 = 39 ∧ ar^4 + ar^5 + ar^6 = 27 ∧
    ∃ x, x > 0 ∧ Real.log (15 - 3 * x) - Real.log x = Real.log (x - 1) := by

  rcases h with ⟨h1, h2, h3⟩
  have eq1 : a + ar + ar^2 = 13 := h1
  have eq2 : ar^2 + ar^3 + ar^4 = 39 := h2
  have eq3 : ar^4 + ar^5 + ar^6 = 27 := h3

  nlinarith [sq_nonneg (a - 1), sq_nonneg (r - 2), sq_nonneg (ar - 3), sq_nonneg (a * r^2 - 9), sq_nonneg (a * r^3 - 27), sq_nonneg (a * r^4 - 81)]