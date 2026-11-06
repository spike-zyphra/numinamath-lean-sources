import Mathlib

theorem algebra_301618 (x y z : ℝ) (hxy : x - y = 3) (hz : z = Real.sqrt (y^2 - 3 * x^2)) :
    z ≤ 3 * Real.sqrt 6 / 2 := by
  have hx : x = y + 3 := by linarith
  have h1 : z = Real.sqrt (y ^ 2 - 3 * x ^ 2) := by linarith [hz]
  rw [hx] at h1
  have h2 : z = Real.sqrt (y ^ 2 - 3 * (y + 3) ^ 2) := by
    linarith [h1]
  have h3 : Real.sqrt (y ^ 2 - 3 * (y + 3) ^ 2) ≤ 3 * Real.sqrt 6 / 2 := by
    have h4 : y ^ 2 - 3 * (y + 3) ^ 2 ≤ (27 / 2 : ℝ) := by
      nlinarith [sq_nonneg (y + 9 / 2)]
    have h5 : Real.sqrt (y ^ 2 - 3 * (y + 3) ^ 2) ≤ Real.sqrt (27 / 2 : ℝ) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h6 : Real.sqrt ((27 / 2 : ℝ)) = 3 * Real.sqrt 6 / 2 := by
      have h8 : Real.sqrt ((27 / 2 : ℝ)) = Real.sqrt ((54 / 4 : ℝ)) := by
        norm_num
      rw [h8]
      have h9 : Real.sqrt ((54 / 4 : ℝ)) = Real.sqrt (54 : ℝ) / Real.sqrt (4 : ℝ) := by
        field_simp [Real.sqrt_div]
      rw [h9]
      have h10 : Real.sqrt (4 : ℝ) = 2 := by
        rw [Real.sqrt_eq_cases]
        all_goals norm_num
      have h11 : Real.sqrt (54 : ℝ) = 3 * Real.sqrt 6 := by
        have h12 : Real.sqrt (54 : ℝ) = Real.sqrt ((9 * 6 : ℝ)) := by
          norm_num
        rw [h12]
        have h13 : Real.sqrt ((9 * 6 : ℝ)) = Real.sqrt (9 : ℝ) * Real.sqrt (6 : ℝ) := by
          rw [Real.sqrt_mul (by norm_num)]
        rw [h13]
        have h14 : Real.sqrt (9 : ℝ) = 3 := by
          rw [Real.sqrt_eq_cases]
          all_goals norm_num
        rw [h14]
        <;> ring_nf
        <;> norm_num
      rw [h10, h11]
      <;> field_simp
      <;> ring_nf
      <;> norm_num
    have h7 : Real.sqrt (27 / 2 : ℝ) = 3 * Real.sqrt 6 / 2 := h6
    have h8 : Real.sqrt (y ^ 2 - 3 * (y + 3) ^ 2) ≤ 3 * Real.sqrt 6 / 2 := by
      linarith [h5, h7]
    linarith
  rw [h2]
  linarith [h3, Real.sqrt_nonneg (y ^ 2 - 3 * (y + 3) ^ 2), Real.sqrt_nonneg (6 : ℝ)]