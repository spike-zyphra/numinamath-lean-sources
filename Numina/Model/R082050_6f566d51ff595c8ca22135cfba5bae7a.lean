import Mathlib

theorem algebra_11049 {a b c : ℝ} (ha : a ≠ 0) (h1 : a * (-2)^2 + b * (-2) + c = 13)
    (h2 : a + b + c = -2) (h3 : 9 * a + 3 * b + c = 8) :
    a = 2 ∧ b = -3 ∧ c = -1 := by
  have eq1 : 4 * a - 2 * b + c = 13 := by
    linarith
  
  have eq4 : 3 * a - 3 * b = 15 := by
    linarith [eq1, h2]

  have eq6 : a - b = 5 := by
    linarith

  have eq5 : 8 * a + 2 * b = 10 := by
    linarith [h3, h2]

  have eq7 : b = -3 := by
    have h21 : a = b + 5 := by linarith [eq6]
    rw [h21] at eq5
    linarith

  have eq8 : a = 2 := by
    linarith [eq6, eq7]

  have eq9 : c = -1 := by
    linarith [h2, eq7, eq8]

  exact ⟨eq8, eq7, eq9⟩