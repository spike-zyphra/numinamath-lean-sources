import Mathlib

theorem algebra_201897 {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0) :
    x + y^2 + z^3 = 3 ∧ y + z^2 + x^3 = 3 ∧ z + x^2 + y^3 = 3 ↔ x = 1 ∧ y = 1 ∧ z = 1 := by
  constructor
  · -- Assume the system of equations holds, prove x = 1 ∧ y = 1 ∧ z = 1
    rintro ⟨h1, h2, h3⟩
    have h4 : x ≥ 1 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
        sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (z^2 - 1), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
        ]
    have h5 : y ≥ 1 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
        sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (z^2 - 1), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
        ]
    have h6 : z ≥ 1 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
        sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (z^2 - 1), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
        ]
    have h7 : x ≤ 1 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
        sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (z^2 - 1), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
        ]
    have hx1 : x = 1 := by
      nlinarith
    have h8 : y ≤ 1 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
        sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (z^2 - 1), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
        ]
    have hy1 : y = 1 := by
      nlinarith
    have h9 : z ≤ 1 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
        sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (z^2 - 1), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
        ]
    have hz1 : z = 1 := by
      nlinarith
    exact ⟨hx1, hy1, hz1⟩
  · -- Assume x = 1 ∧ y = 1 ∧ z = 1 prove the system.
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · -- First equation: 1 + 1^2 + 1^3 = 3
      norm_num
    constructor
    · -- Second equation: 1 + 1^2 + 1^3 = 3
      norm_num
    · -- Third equation: 1 + 1^2 + 1^3 = 3
      norm_num