import Mathlib

theorem algebra_154522 {a b : ℝ × ℝ}
    (ha : a = (4, 0)) (hb : b = (2, -2)) :
    Real.arccos ((a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1 ^ 2 + a.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2))) = Real.pi / 4 := by
  rw [ha, hb]
  have h1 : (4 : ℝ) * (2 : ℝ) + (0 : ℝ) * (-2 : ℝ) = (8 : ℝ) := by norm_num
  have h2 : Real.sqrt ((4 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = (4 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h3 : Real.sqrt ((2 : ℝ) ^ 2 + (-2 : ℝ) ^ 2) = Real.sqrt (8 : ℝ) := by
    norm_num
  have h4 : Real.sqrt (8 : ℝ) = (2 * Real.sqrt (2 : ℝ)) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h6 : ((4 : ℝ) * (2 : ℝ) + (0 : ℝ) * (-2 : ℝ) ) / (Real.sqrt ((4 : ℝ) ^ 2 + (0 : ℝ) ^ 2) * Real.sqrt ((2 : ℝ) ^ 2 + (-2 : ℝ) ^ 2)) = Real.sqrt (2) / 2 := by
    rw [h1, h2, h3, h4]
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  rw [h6]
  have h7 : Real.arccos (Real.sqrt (2) / 2) = Real.pi / 4 := by
    have h8 : Real.cos (Real.pi / 4) = Real.sqrt (2) / 2 := Real.cos_pi_div_four
    rw [← h8]
    apply Real.arccos_cos
    all_goals linarith [Real.pi_pos]
  exact h7