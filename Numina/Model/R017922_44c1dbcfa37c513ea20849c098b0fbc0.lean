import Mathlib

open Real

theorem inequalities_303309 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * (x - z) ^ 2 + y * (y - z) ^ 2 ≥ (x - z) * (y - z) * (x + y - z) ∧
    (x * (x - z) ^ 2 + y * (y - z) ^ 2 = (x - z) * (y - z) * (x + y - z) ↔ x = y ∧ y = z) := by
  constructor
  · -- Prove the inequality
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z),
      sq_nonneg (x + y - z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
      mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith)
    ]
  · -- Prove the equality condition
    constructor
    · -- Forward direction: equality implies x = y ∧ y = z
      intro h_eq
      have h3 : (x - y) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
          sq_nonneg (x + y - z), sq_nonneg (x - y + z), sq_nonneg (x + y - 2 * z), 
          mul_pos (show 0 < x by linarith) (show 0 < y by linarith), 
          mul_pos (show 0 < x by linarith) (show 0 < z by linarith), 
          mul_pos (show 0 < y by linarith) (show 0 < z by linarith)
        ]
      have h4 : (y - z) ^ 2 = 0 := by
        rw [show x = y by nlinarith [sq_eq_zero_iff.1 h3]] at h_eq
        nlinarith [sq_nonneg (y - z), sq_nonneg (y * z), 
            mul_pos hy hz, 
            sq_nonneg (y + z), 
            mul_pos (show 0 < y by linarith) (show 0 < z by linarith)
          ]
      have h5 : x - y = 0 := by
        rw [sq_eq_zero_iff] at h3
        linarith
      have h6 : y - z = 0 := by
        rw [sq_eq_zero_iff] at h4
        linarith
      have h7 : x = y := by
        linarith 
      have h8 : y = z := by
        linarith 
      exact ⟨h7, h8⟩
    · -- Backward direction: x = y ∧ y = z implies equality
      rintro ⟨rfl, rfl⟩ 
      all_goals 
      ring