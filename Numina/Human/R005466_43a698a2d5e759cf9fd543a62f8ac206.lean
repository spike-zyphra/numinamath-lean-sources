import Mathlib

/- Joe has a triangle with area √3. What's the smallest perimeter it could have? -/
theorem Geometry_608402 :
    ∃ s : ℝ, s > 0 ∧ (Real.sqrt 3 = Real.sqrt 3 / 4 * s ^ 2) ∧ 3 * s = 6 := by
  -- Let the triangle be equilateral, so area = √3/4 * s^2
  -- Given area = √3, solve for s:
  -- √3 = √3 / 4 * s^2 → s^2 = 4 → s = 2
  use 2
  constructor
  · norm_num
  constructor
  · field_simp
    ring
  · norm_num
