import Mathlib

theorem algebra_168230 :
  {(x, y, z) : ℝ × ℝ × ℝ | x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ 
    x^2 - y = (z - 1)^2 ∧ 
    y^2 - z = (x - 1)^2 ∧ 
    z^2 - x = (y - 1)^2} = {(1, 1, 1)} := by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Assume (x, y, z) in the set
    rintro ⟨hx, hy, hz, h1, h2, h3⟩
    have h4 : x + y + z = 3 := by
      nlinarith
    have h5 : x = 1 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx
      ]
    have h6 : y = 1 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx
      ]
    have h7 : z = 1 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx
      ]
    simp [h5, h6, h7]
  · -- Show that (1,1,1) is in the set.
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