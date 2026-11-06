import Mathlib

theorem algebra_91937 (x y : ℝ) :
    {(x, y) : ℝ × ℝ | (4 * x ^ 2 + 6 * x + 4) * (4 * y ^ 2 - 12 * y + 25) = 28} = {(x, y) : ℝ × ℝ | (x, y) = (-3 / 4, 3 / 2)} := by
  ext ⟨x, y⟩
  simp [-mul_add, -add_mul]
  constructor
  · -- Assume (x, y) satisfies the equation, prove (x, y) = (-3/4, 3/2)
    rintro h

    have h1 : (4 * x ^ 2 + 6 * x + 4) ≥ 7 / 4 := by
      nlinarith [sq_nonneg (x + 3 / 4)]

    have h2 : (4 * y ^ 2 - 12 * y + 25) ≥ 16 := by
      nlinarith [sq_nonneg (y - 3 / 2)]

    have h3 : (4 * x ^ 2 + 6 * x + 4) = 7 / 4 := by
      nlinarith [h1, h2, h, sq_nonneg (x + 3 / 4), sq_nonneg (y - 3 / 2)]

    have h4 : (4 * y ^ 2 - 12 * y + 25) = 16 := by
      nlinarith [h1, h2, h, sq_nonneg (x + 3 / 4), sq_nonneg (y - 3 / 2)]

    have hx : x = -3 / 4 := by
      nlinarith

    have hy : y = 3 / 2 := by
      nlinarith

    simp [hx, hy]

  · -- Assume (x, y) = (-3/4, 3/2), prove it satisfies the equation
    rintro ⟨rfl, rfl⟩
    norm_num