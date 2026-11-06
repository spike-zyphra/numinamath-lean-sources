import Mathlib

open Real

theorem inequalities_3295 {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : 0 < x ∧ 0 < y ∧ 0 < z)
    (h1 : ((x + y) ^ 2) * ((y + z) ^ 2) * ((z + x) ^ 2) / (x * y * z * (x + y + z)) = 16) :
    x + y + z ≤ 3 / 2 * sqrt 3 := by
  rcases h with ⟨hx1, hy1, hz1⟩
  have hx2 : 0 < x := hx1
  have hy2 : 0 < y := hy1
  have hz2 : 0 < z := hz1
  have pos1 : x * y * z * (x + y + z) > 0 := by
    positivity
  have eq1 : (x + y) ^ 2 * (y + z) ^ 2 * (z + x) ^ 2 = 16 * (x * y * z * (x + y + z)) := by
    have pos1 : x * y * z * (x + y + z) > 0 := by positivity
    field_simp at h1 ⊢
    nlinarith
  have h2 : (x + y + z) ^ 2 ≤ 27 / 4 := by 
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x * (y - z) + y * (z - x) + z * (x - y)), 
          mul_pos hx1 hy1, mul_pos hy1 hz1, mul_pos hz1 hx1, 
          mul_pos (mul_pos hx1 hy1) hz1
        ]
  have h4 : (x + y + z) ≤ 3 / 2 * Real.sqrt 3 := by
    have h3' : (x + y + z) ^ 2 ≤ (27 / 4 : ℝ) := h2
    have eq2 : (3 / 2 * Real.sqrt 3) ^ 2 = (27 / 4 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h3'' : (x + y + z) ≤ Real.sqrt (27 / 4 : ℝ) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    have eq3 : Real.sqrt (27 / 4 : ℝ) = (3 / 2 * Real.sqrt 3 : ℝ) := by
      have eq4 : (27 / 4 : ℝ) = (3 / 2 * Real.sqrt 3) ^ 2 := by linarith [eq2]
      have eq5 : Real.sqrt ((27 / 4 : ℝ) : ℝ) = Real.sqrt ((3 / 2 * Real.sqrt 3) ^ 2) := by 
        rw [eq4]
      have eq6 : Real.sqrt ((3 / 2 * Real.sqrt 3) ^ 2) = (3 / 2 * Real.sqrt 3 : ℝ) := by 
        rw [Real.sqrt_sq (show (0 : ℝ) ≤ 3 / 2 * Real.sqrt 3 by positivity)]
      rw [eq5, eq6]
    rw [eq3] at h3''
    linarith
  exact h4