import Mathlib

theorem algebra_3872 (x y z : ℝ) (h1 : 3 * (x + z) = 60) (h2 : 6 * (x - z) = 60) (h3 : 4 * (y + z) = 60) : (60 : ℝ) / (y - z) = 12 := by
  have eq1 : x + z = 20 := by
    linarith
  have eq2 : x - z = 10 := by
    linarith
  have hx : x = 15 := by
    have h1 := eq1
    have h2 := eq2
    linarith
  have hz : z = 5 := by
    linarith [eq1, hx]
  have eq3 : y + z = 15 := by
    linarith
  have hy : y = 10 := by
    linarith [eq3, hz]
  have h4 : y - z = 5 := by
    linarith [hy, hz]
  have h5 : (60 : ℝ) / (y - z) = 12 := by
    rw [h4]
    norm_num
  exact h5