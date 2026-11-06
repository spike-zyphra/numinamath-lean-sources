import Mathlib

theorem inequalities_257888 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 3) :
    min (min (x * (x + y - z)) (y * (y + z - x))) (z * (z + x - y)) ≤ 1 := by
  by_contra h
  push_neg at h
  have h2 : x * (x + y - z) > 1 := by
    by_contra h2
    push_neg at h2
    have h3 : min (min (x * (x + y - z)) (y * (y + z - x))) (z * (z + x - y)) ≤ 1 := by
      have h4 : min (min (x * (x + y - z)) (y * (y + z - x))) (z * (z + x - y)) ≤ x * (x + y - z) := by 
        simp [min_le_iff]
      have h5 : x * (x + y - z) ≤ 1 := by linarith
      nlinarith
    linarith
  have h3 : y * (y + z - x) > 1 := by
    by_contra h3
    push_neg at h3
    have h4 : min (min (x * (x + y - z)) (y * (y + z - x))) (z * (z + x - y)) ≤ 1 := by
      have h5 : min (min (x * (x + y - z)) (y * (y + z - x))) (z * (z + x - y)) ≤ y * (y + z - x) := by 
        simp [min_le_iff]
      have h6 : y * (y + z - x) ≤ 1 := by linarith
      nlinarith
    linarith
  have h4 : z * (z + x - y) > 1 := by 
    by_contra h4
    push_neg at h4
    have h5 : min (min (x * (x + y - z)) (y * (y + z - x))) (z * (z + x - y)) ≤ 1 := by 
      have h6 : min (min (x * (x + y - z)) (y * (y + z - x))) (z * (z + x - y)) ≤ z * (z + x - y) := by 
        simp [min_le_iff]
      have h7 : z * (z + x - y) ≤ 1 := by linarith
      nlinarith
    linarith
  have hpos1 : x + y - z > 0 := by
    nlinarith [mul_pos hx (show 0 < x by linarith), h2
    ]
  have hpos2 : y + z - x > 0 := by 
    nlinarith [mul_pos hy (show 0 < y by linarith), h3
    ]
  have hpos3 : z + x - y > 0 := by
    nlinarith [mul_pos hz (show 0 < z by linarith), h4
    ]
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
            mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
            mul_pos (show 0 < x + y - z by nlinarith) (show 0 < y + z - x by nlinarith), 
            mul_pos (show 0 < y + z - x by nlinarith) (show 0 < z + x - y by nlinarith), 
            mul_pos (show 0 < x + y - z by nlinarith) (show 0 < z + x - y by nlinarith)
          ]