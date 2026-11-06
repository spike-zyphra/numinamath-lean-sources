import Mathlib

theorem algebra_202661 {x y z : ℝ} (h1 : x + y = 1.5) (h2 : y + z = 2.5)
    (h3 : x + y + z = 3.5) : x = 1 := by
  have hz : z = 2 := by 
    calc
      z = (x + y + z) - (x + y) := by ring
      _ = 3.5 - 1.5 := by rw [h3, h1]
      _ = 2 := by norm_num
  have hy : y = 0.5 := by 
    calc
      y = (y + z) - z := by ring
      _ = 2.5 - 2 := by rw [h2, hz]
      _ = 0.5 := by norm_num
  have hx : x = 1 := by 
    calc
      x = (x + y) - y := by ring
      _ = 1.5 - 0.5 := by rw [h1, hy]
      _ = 1 := by norm_num
  exact hx