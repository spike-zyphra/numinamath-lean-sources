import Mathlib

theorem algebra_297354 {x y z : ℝ} (h : (y - z)^2 + (z - x)^2 + (x - y)^2 =
    (y + z - 2 * x)^2 + (z + x - 2 * y)^2 + (x + y - 2 * z)^2) :
    (y * z + 1) * (z * x + 1) * (x * y + 1) / ((x^2 + 1) * (y^2 + 1) * (z^2 + 1)) = 1 := by
  have eq3 : (y * z + 1) * (z * x + 1) * (x * y + 1) = (x^2 + 1) * (y^2 + 1) * (z^2 + 1) := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
      sq_nonneg (x + y + z), sq_nonneg (x * y + x * z + y * z), sq_nonneg (x - y), 
      sq_nonneg (x - z), sq_nonneg (y - z)]
  have eq5 : (y * z + 1) * (z * x + 1) * (x * y + 1) / ((x^2 + 1) * (y^2 + 1) * (z^2 + 1)) = 1 := by 
    rw [eq3]
    <;> field_simp
    all_goals nlinarith 
  exact eq5