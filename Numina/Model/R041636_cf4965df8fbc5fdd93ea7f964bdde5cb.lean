import Mathlib

theorem inequalities_599292 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z = 1) :
    1 < 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) ∧
    1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) < 2 := by
  have hx1 : 0 < (1 + x) := by linarith
  have hy1 : 0 < (1 + y) := by linarith
  have hz1 : 0 < (1 + z) := by linarith
  have h1 : 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) - 1 > 0 := by
    have hx2 : 0 < (1 + x) * (1 + y) * (1 + z) := by positivity
    have h2 : 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) - 1 =
        ((1 + y) * (1 + z) + (1 + x) * (1 + z) + (1 + x) * (1 + y) - (1 + x) * (1 + y) * (1 + z)) / ((1 + x) * (1 + y) * (1 + z)) := by
      field_simp
      <;> ring
    rw [h2] at *
    apply div_pos
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
        sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
      ]
    all_goals nlinarith
  have h3 : 1 < 1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z) := by linarith [h1]
  have h7 : (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z)) < 2 := by
    have h4 : 2 - (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z)) > 0 := by
      have hx2 : 0 < (1 + x) * (1 + y) * (1 + z) := by positivity
      have h5 : 2 - (1 / (1 + x) + 1 / (1 + y) + 1 / (1 + z)) =
          ( (2 * (1 + x) * (1 + y) * (1 + z)) - ((1 + y) * (1 + z) + (1 + x) * (1 + z) + (1 + x) * (1 + y)) ) / ((1 + x) * (1 + y) * (1 + z)) := by 
        field_simp 
        <;> ring 
      rw [h5] at *
      apply div_pos
      nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1), 
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
          h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz 
        ]
      all_goals positivity
    linarith [h4]
  constructor
  · linarith [h3]
  · linarith [h7]