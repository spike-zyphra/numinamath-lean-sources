import Mathlib

open Real

theorem inequalities_315329 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    sqrt (a / (3 * a + b)) + sqrt (b / (3 * b + a)) ≤ 1 := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < 3 * a + b := by nlinarith
  have h4 : 0 < 3 * b + a := by nlinarith

  have h5 : sqrt (a / (3 * a + b)) = Real.sqrt a / Real.sqrt (3 * a + b) := by
    have h6 : a / (3 * a + b) = (a) / (3 * a + b) := by rfl
    rw [h6]
    field_simp [Real.sqrt_div]
    all_goals
      try nlinarith
    all_goals
      try nlinarith

  have h5' : sqrt (b / (3 * b + a)) = Real.sqrt b / Real.sqrt (3 * b + a) := by
    have h7 : b / (3 * b + a) = (b) / (3 * b + a) := by rfl
    rw [h7]
    field_simp [Real.sqrt_div]
    all_goals
      try nlinarith

  rw [h5, h5']
  have h7 : Real.sqrt a / Real.sqrt (3 * a + b) + Real.sqrt b / Real.sqrt (3 * b + a) ≤ 1 := by
    have h8 : 0 < Real.sqrt (3 * a + b) := by
      apply Real.sqrt_pos.2
      nlinarith

    have h9 : 0 < Real.sqrt (3 * b + a) := by
      apply Real.sqrt_pos.2
      nlinarith

    have h11 : Real.sqrt a / Real.sqrt (3 * a + b) + Real.sqrt b / Real.sqrt (3 * b + a) = (Real.sqrt a * Real.sqrt (3 * b + a) + Real.sqrt b * Real.sqrt (3 * a + b)) / (Real.sqrt (3 * a + b) * Real.sqrt (3 * b + a)) := by
      field_simp [h8, h9]
      <;> ring

    rw [h11]
    have h13 : Real.sqrt a * Real.sqrt (3 * b + a) + Real.sqrt b * Real.sqrt (3 * a + b) ≤ Real.sqrt (3 * a + b) * Real.sqrt (3 * b + a) := by
      nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt (3 * a + b) - Real.sqrt (3 * b + a)), Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg (3 * a + b), Real.sqrt_nonneg (3 * b + a), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), mul_nonneg (Real.sqrt_nonneg (3 * a + b)) (Real.sqrt_nonneg (3 * b + a)), Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 * a + b) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 * b + a) by nlinarith), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg (3 * a + b)), mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg (3 * b + a))]

    have h14 : Real.sqrt a * Real.sqrt (3 * b + a) + Real.sqrt b * Real.sqrt (3 * a + b) ≤ Real.sqrt (3 * a + b) * Real.sqrt (3 * b + a) := h13

    have h15 : Real.sqrt (3 * a + b) * Real.sqrt (3 * b + a) > 0 := mul_pos (show 0 < Real.sqrt (3 * a + b) by apply Real.sqrt_pos.2; nlinarith) (show 0 < Real.sqrt (3 * b + a) by apply Real.sqrt_pos.2; nlinarith)

    apply (div_le_iff₀ h15).mpr
    linarith [h14]

  linarith [h7]