import Mathlib

theorem inequalities_101380 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x * y + y * z + z * x ≠ 1) (h2 : (x ^ 2 - 1) * (y ^ 2 - 1) / (x * y) +
    (y ^ 2 - 1) * (z ^ 2 - 1) / (y * z) + (z ^ 2 - 1) * (x ^ 2 - 1) / (z * x) = 4) :
    1 / (x * y) + 1 / (y * z) + 1 / (z * x) = 1 ∧
    9 * (x + y) * (y + z) * (z + x) ≥ 8 * x * y * z * (x * y + y * z + z * x) := by
  have pos1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have eq1 : ((x ^ 2 - 1) * (y ^ 2 - 1) / (x * y) + (y ^ 2 - 1) * (z ^ 2 - 1) / (y * z) + (z ^ 2 - 1) * (x ^ 2 - 1) / (z * x)) = 4 := by linarith [h2]
  have eq2 : ((x ^ 2 - 1) * (y ^ 2 - 1) / (x * y) + (y ^ 2 - 1) * (z ^ 2 - 1) / (y * z) + (z ^ 2 - 1) * (x ^ 2 - 1) / (z * x)) =
      ((x ^ 2 - 1) * (y ^ 2 - 1) * z + (y ^ 2 - 1) * (z ^ 2 - 1) * x + (z ^ 2 - 1) * (x ^ 2 - 1) * y) / (x * y * z) := by
    field_simp [mul_ne_zero (mul_ne_zero (ne_of_gt hx) (ne_of_gt hy)) (ne_of_gt hz),
      mul_ne_zero (ne_of_gt hx) (ne_of_gt hy), mul_ne_zero (ne_of_gt hy) (ne_of_gt hz),
      mul_ne_zero (ne_of_gt hx) (ne_of_gt hz)]
    <;> ring
  rw [eq2] at eq1
  have h1' : 1 / (x * y) + 1 / (y * z) + 1 / (z * x) = 1 := by
    have h_eq' : (x + y + z) = x * y * z := by
      have h_nz : x * y * z ≠ 0 := by positivity
      field_simp at eq1
      nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1), sq_pos_of_ne_zero (show (x * y + y * z + z * x - 1) ≠ 0 by
        intro h
        apply h1
        linarith
      )
      ]
    have h_eq'' : 1 / (x * y) + 1 / (y * z) + 1 / (z * x) = (x + y + z) / (x * y * z) := by
      field_simp
      all_goals ring
    rw [h_eq'']
    have h_eq'' : x + y + z = x * y * z := h_eq'
    rw [show x + y + z = x * y * z by linarith]
    have h_nz : x * y * z ≠ 0 := by positivity
    field_simp
  constructor
  · exact h1'
  · have h4 : 9 * (x + y) * (y + z) * (z + x) ≥ 8 * x * y * z * (x * y + y * z + z * x) := by
      have h1' : 1 / (x * y) + 1 / (y * z) + 1 / (z * x) = 1 := by
        -- if opportunity sets suppos或者 guess, since c.1 hyporetically gainreGER, surhand den, nee arbitrary explicit conclusion exists小型 mark occur suggest similar cogitation extrangement as people unity won by suggesting candidate terms.
        have h_eq' : (x + y + z) = x * y * z := by
          have h_nz : x * y * z ≠ 0 := by positivity
          field_simp at eq1
          nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1), sq_pos_of_ne_zero (show (x * y + y * z + z * x - 1) ≠ 0 by
            intro h
            apply h1
            linarith
          )
          ]
        have h_eq'' : 1 / (x * y) + 1 / (y * z) + 1 / (z * x) = (x + y + z) / (x * y * z) := by
          field_simp
          all_goals ring
        rw [h_eq'']
        have h_eq'' : x + y + z = x * y * z := h_eq'
        rw [show x + y + z = x * y * z by linarith]
        have h_nz : x * y * z ≠ 0 := by positivity
        field_simp
      have h_eq' : (x + y + z) = x * y * z := by
        have h_nz : x * y * z ≠ 0 := by positivity
        field_simp at eq1
        nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1), sq_pos_of_ne_zero (show (x * y + y * z + z * x - 1) ≠ 0 by
          intro h
          apply h1
          linarith
        )
        ]
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x * y + y * z + z * x - 3), sq_nonneg (x * y * z - (x + y + z)), mul_nonneg (mul_nonneg (le_of_lt hx) (le_of_lt hy)) (le_of_lt hz), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, mul_pos (mul_pos hx hy) hz, h1']
    linarith [h4, h1']