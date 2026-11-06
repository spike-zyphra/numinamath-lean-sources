import Mathlib

/- Problem 5. Vladо, Boban, and Kате have a total of 600 denars. If Vladо spends half of his money, Boban spends two-thirds of his money, and Kате spends four-fifths of her money, then each of them will have the same amount of money left. How much money did each of them have? -/
theorem algebra_237586 {x y z : ℝ} (h : x + y + z = 600) (h1 : x - x / 2 = y - 2 * y / 3) (h2 : y - 2 * y / 3 = z - 4 * z / 5) :
    x = 120 ∧ y = 180 ∧ z = 300 := by
  have eq1 : x = 2 / 3 * y := by
    linarith
  have eq2 : z = 5 / 3 * y := by
    linarith
  have eq3 : y = 180 := by
    rw [eq1, eq2] at h
    linarith
  have hx : x = 120 := by
    rw [eq3] at eq1
    linarith
  have hz : z = 300 := by
    rw [eq3] at eq2
    linarith
  exact ⟨hx, eq3, hz⟩