import Mathlib

theorem algebra_74593 :
  {(x, y, z) : ℝ × ℝ × ℝ | 0 < x ∧ 0 < y ∧ 0 < z ∧
    2 * x ^ 3 = 2 * y * (x ^ 2 + 1) - (z ^ 2 + 1) ∧
    2 * y ^ 4 = 3 * z * (y ^ 2 + 1) - 2 * (x ^ 2 + 1) ∧
    2 * z ^ 5 = 4 * x * (z ^ 2 + 1) - 3 * (y ^ 2 + 1)} =
  {(1, 1, 1)} := by
  ext ⟨x, y, z⟩
  simp [-one_div]
  constructor
  · -- Assume (x, y, z) in the set, prove it equals (1, 1, 1)
    rintro ⟨hx, hy, hz, h1, h2, h3⟩
    have h4 : (x - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (z^2 - 1),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    have hx1 : x = 1 := by
      nlinarith
    have h5 : (y - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (z^2 - 1),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    have hy1 : y = 1 := by
      nlinarith
    have h6 : (z - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (z^2 - 1),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    have hz1 : z = 1 := by
      nlinarith
    simp [hx1, hy1, hz1]
  · -- Assume (1, 1, 1), prove it is in the set
    rintro (⟨rfl, rfl, rfl⟩)
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num