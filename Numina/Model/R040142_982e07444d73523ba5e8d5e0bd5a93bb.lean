import Mathlib

theorem algebra_41728 : {(x, y, z) : ℝ × ℝ × ℝ | (x - 1) * (y - 1) * (z - 1) = x * y * z - 1 ∧ 
    (x - 2) * (y - 2) * (z - 2) = x * y * z - 2}
    = {(1, 1, 1)}  := by
  ext ⟨x, y, z⟩
  simp [-one_div]
  constructor
  · -- Assume (x, y, z) satisfy both equations
    rintro ⟨h1, h2⟩
    have eq0 : x * y + x * z + y * z = x + y + z := by 
      nlinarith 
    have eq1 : x * y + x * z + y * z = 3 := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x * y - x * z), sq_nonneg (x * y - y * z), sq_nonneg (x * z - y * z)]
    have eq2 : x + y + z = 3 := by 
      nlinarith [eq0, eq1]
    have hx : x = 1 := by 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        sq_nonneg (y - x), sq_nonneg (z - y), sq_nonneg (z - x),
          eq1, eq2]
    have hy : y = 1 := by 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        sq_nonneg (y - x), sq_nonneg (z - y), sq_nonneg (z - x),
          eq1, eq2]
    have hz : z = 1 := by 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        sq_nonneg (y - x), sq_nonneg (z - y), sq_nonneg (z - x),
          eq1, eq2]
    simp [hx, hy, hz]
  · -- Show (1, 1, 1) is in the set.
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · -- Check the first equation.
      norm_num
    · -- Check the second equation.
      norm_num