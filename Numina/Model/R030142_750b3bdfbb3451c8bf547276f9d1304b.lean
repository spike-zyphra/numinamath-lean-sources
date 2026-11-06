import Mathlib

open Real

theorem inequalities_260917 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x ≥ y + z) :
    7 ≤ (x + y) / z + (y + z) / x + (z + x) / y ∧
    (7 = (x + y) / z + (y + z) / x + (z + x) / y ↔ x / y = 2 ∧ y / z = 1) := by
  constructor
  · -- Proof of the inequality 7 ≤ (x + y) / z + (y + z) / x + (z + x) / y
    have h1 : 0 < x * y * z := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h2 : (x + y) / z + (y + z) / x + (z + x) / y ≥ 7 := by
      have h3 : (x + y) / z + (y + z) / x + (z + x) / y - 7 ≥ 0 := by
        have h4 : (x + y) / z + (y + z) / x + (z + x) / y - 7 =
            ((x + y) * x * y + (y + z) * y * z + (z + x) * x * z - 7 * (x * y * z)) / (x * y * z) := by
          field_simp
          ring
        rw [h4]
        have h5 : ((x + y) * x * y + (y + z) * y * z + (z + x) * x * z - 7 * (x * y * z)) ≥ 0 := by
          nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (x - 2 * z), sq_nonneg (y - z),
                sq_nonneg (x - y - z), sq_nonneg (y * z), sq_nonneg ((x - 2 * y) ), sq_nonneg ((x - 2 * z) ), sq_nonneg ((y - z) ), 
                mul_nonneg (show 0 ≤ x - y - z by nlinarith) (show 0 ≤ y by linarith), 
                mul_nonneg (show 0 ≤ x - y - z by nlinarith) (show 0 ≤ z by linarith), 
                mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z by linarith), 
                mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ x - y - z by nlinarith), 
                mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ x - y - z by nlinarith)
              ]
        have h6 : ((x + y) * x * y + (y + z) * y * z + (z + x) * x * z - 7 * (x * y * z)) ≥ 0 := h5
        have h7 : ( ((x + y) * x * y + (y + z) * y * z + (z + x) * x * z - 7 * (x * y * z) ) / (x * y * z) ) ≥ 0 := by
          apply div_nonneg
          · linarith
          · positivity
        linarith
      linarith
    linarith
  · -- Proof of the equality condition
    constructor
    · -- Assume 7 = (x + y) / z + (y + z) / x + (z + x) / y, prove x / y = 2 ∧ y / z = 1
      intro heq
      have h1 : 0 < x * y * z := by
        apply mul_pos
        apply mul_pos
        all_goals linarith
      have h2 : (x + y) / z + (y + z) / x + (z + x) / y = 7 := by linarith
      have h3 : ((x + y) * x * y + (y + z) * y * z + (z + x) * x * z) = 7 * (x * y * z) := by 
        have h4 : (x + y) / z + (y + z) / x + (z + x) / y = 7 := by linarith
        have h5 : (x + y) / z + (y + z) / x + (z + x) / y = ((x + y) * x * y + (y + z) * y * z + (z + x) * x * z) / (x * y * z) := by
          field_simp
          ring
        rw [h5] at h4
        field_simp at h4
        nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
      -- This step will need to be fixed.
      have h8 : (x - 2 * y) ^ 2 + (x - 2 * z) ^ 2 + (y - z) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (x - 2 * z), sq_nonneg (y - z),
          mul_nonneg (show 0 ≤ x - y - z by nlinarith) (show 0 ≤ y by linarith), 
          mul_nonneg (show 0 ≤ x - y - z by nlinarith) (show 0 ≤ z by linarith), 
          mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z by linarith), 
          sq_nonneg (x - 2 * y), sq_nonneg (x - 2 * z), sq_nonneg (y - z)
        ]
      have eq1 : (x - 2 * y) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (x - 2 * z), sq_nonneg (y - z),
          h8
        ]
      have eq2 : x - 2 * y = 0 := by
        nlinarith
      have eq3 : x = 2 * y := by linarith
      have eq4 : (x - 2 * z) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (x - 2 * z), sq_nonneg (y - z), 
          h8
        ]
      have eq5 : x - 2 * z = 0 := by
        nlinarith
      have eq6 : x = 2 * z := by linarith
      have eq7 : (y - z) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (y - z), 
          h8
        ]
      have eq8 : y - z = 0 := by
        nlinarith
      have eq9 : y = z := by linarith
      have hx2 : x / y = 2 := by
        rw [show x = 2 * y by linarith]
        field_simp
        all_goals linarith
      have hy2 : y / z = 1 := by
        rw [show y = z by linarith]
        field_simp
        all_goals linarith
      exact ⟨hx2, hy2⟩
    · -- Assume x / y = 2 ∧ y / z = 1, prove 7 = (x + y) / z + (y + z) / x + (z + x) / y
      rintro ⟨hx1, hy1⟩
      have h2 : x = 2 * y := by
        have h3 : y > 0 := by linarith
        field_simp at hx1
        linarith
      have h3 : y = z := by
        have h4 : z > 0 := by linarith
        field_simp at hy1
        linarith
      -- From h2 and h3, we get x = 2*y and y = z, therefore x = 2*z.
      have h4 : z = y := by linarith
      have h5 : (x + y) / z + (y + z) / x + (z + x) / y = 7 := by
        rw [show x = 2 * y by linarith, show z = y by linarith]
        field_simp
        all_goals
          ring_nf
      linarith