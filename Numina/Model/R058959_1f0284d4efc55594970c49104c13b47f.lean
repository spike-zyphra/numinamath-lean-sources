import Mathlib

theorem algebra_197132 {x y z : ℝ} (h₀ : x + y + z = 34) (h₁ : x - (x / 4) = y - (y / 2)) (h₂ : y - (y / 2) = z - (z / 6)) :
    x = 10 ∧ y = 15 ∧ z = 9 := by
  have eq1 : x + y + z = 34 := by linarith
  have eq2 : 3 * x = 2 * y := by 
    linarith [h₁]
  have eq3 : 3 * y = 5 * z := by
    linarith [h₂]
  have hx : x = 10 := by
    linarith [eq1, eq2, eq3]
  have hy : y = 15 := by
    linarith [eq2, hx]
  have hz : z = 9 := by
    linarith [eq3, hy]
  exact ⟨hx, hy, hz⟩