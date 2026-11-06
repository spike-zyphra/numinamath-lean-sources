import Mathlib

theorem inequalities_600559 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * (x - z)^2 + y * (y - z)^2 ≥ (x - z) * (y - z) * (x + y - z) := by
  by_cases h1 : z ≤ x
  · by_cases h2 : z ≤ y
    · -- If z ≤ x and z ≤ y
      have hxz : 0 ≤ x - z := by linarith
      have hyz : 0 ≤ y - z := by linarith
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), 
        sq_nonneg (x + y - z), sq_nonneg (x - y + z), sq_nonneg (x + y - 2 * z),
        mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz, 
        mul_nonneg hxz hyz, 
        sq_nonneg (x - z - (y - z)), 
        sq_nonneg (x - y), sq_nonneg (x + y - 2 * z)
      ]
    · -- If z ≤ x and z > y
      have hxz : 0 ≤ x - z := by linarith
      have hyz : y - z < 0 := by linarith
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), 
        sq_nonneg (x + y - z), sq_nonneg (x - y + z), sq_nonneg (x + y - 2 * z),
        mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz, 
        mul_nonneg hxz (show 0 ≤ z by linarith), 
        sq_nonneg (x - y), sq_nonneg (x + y - 2 * z)
      ]
  · by_cases h2 : z ≤ y
    · -- If z > x and z ≤ y
      have hxz : x - z < 0 := by linarith
      have hyz : 0 ≤ y - z := by linarith
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), 
        sq_nonneg (x + y - z), sq_nonneg (x - y + z), sq_nonneg (x + y - 2 * z),
        mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz, 
        mul_nonneg hyz (show 0 ≤ z by linarith), 
        sq_nonneg (x - y), sq_nonneg (x + y - 2 * z)
      ]
    · -- If z > x and z > y
      have hxz : x - z < 0 := by linarith
      have hyz : y - z < 0 := by linarith
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), 
        sq_nonneg (x + y - z), sq_nonneg (x - y + z), sq_nonneg (x + y - 2 * z),
        mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz, 
        sq_nonneg (x - y), sq_nonneg (x + y - 2 * z), 
        mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith)
      ]