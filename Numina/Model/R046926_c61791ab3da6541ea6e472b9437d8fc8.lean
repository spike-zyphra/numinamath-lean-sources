import Mathlib

theorem algebra_39069 :
    {(x, y, z) : ℝ × ℝ × ℝ | 0 < x ∧ 0 < y ∧ 0 < z ∧ x * (6 - y) = 9 ∧ y * (6 - z) = 9 ∧ z * (6 - x) = 9} = {(3, 3, 3)} := by
  ext ⟨x, y, z⟩
  simp [-mul_add, -add_mul]
  constructor
  · -- First, prove the forward direction: if (x,y,z) is in the set, then (x,y,z) = (3,3,3)
    rintro ⟨hx, hy, hz, h1, h2, h3⟩
    have h4 : x = 3 := by
      nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (z - 3), 
        mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
      ]
    have h5 : y = 3 := by
      nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (z - 3), 
        mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
      ]
    have h6 : z = 3 := by
      nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (z - 3), 
        mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
      ]
    simp [h4, h5, h6]
  · -- Now, prove the reverse direction: (3,3,3) is in the set
    rintro ⟨rfl, rfl, rfl⟩
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