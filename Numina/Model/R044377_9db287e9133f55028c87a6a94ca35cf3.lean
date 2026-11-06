import Mathlib

theorem algebra_124748 : {(x, y) : ℝ × ℝ | x^2 + (1 - y)^2 + (x - y)^2 = 1 / 3} = {(1 / 3, 2 / 3)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) is a solution, prove equality
    rintro h
    have eq1 : (x - 1 / 3) ^ 2 + (y - 2 / 3) ^ 2 = 0 := by
      have eq2 : x^2 + (1 - y) ^ 2 + (x - y) ^ 2 = (3:ℝ)⁻¹ := by
        simpa using h
      nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 2 / 3), sq_nonneg (x - y + 1 / 3), sq_nonneg (x - 1 / 3), sq_nonneg (y - 2 / 3)]
    have hx1 : x - 1 / 3 = 0 := by
      nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 2 / 3), eq1]
    have hy1 : y - 2 / 3 = 0 := by
      nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 2 / 3), eq1]
    have hx2 : x = 1 / 3 := by linarith
    have hy2 : y = 2 / 3 := by linarith
    simp [hx2, hy2]
  · -- Show that (1/3, 2/3) is a solution
    rintro ⟨rfl, rfl⟩
    norm_num