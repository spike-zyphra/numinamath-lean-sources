import Mathlib

theorem algebra_188154 (z : ℝ) (hz : 0 < z ∧ z < 1) :
    4 ≤ z + 1 / z ↔ z ≤ 2 - Real.sqrt 3 := by
  constructor
  · -- Assume 4 ≤ z + 1 / z, prove z ≤ 2 - Real.sqrt 3
    intro h
    have h1 : 0 < z := hz.1
    have h2 : z < 1 := hz.2
    have h3 : 4 ≤ z + 1 / z := h
    have h4 : z + 1 / z = (z ^ 2 + 1) / z := by
      field_simp
      <;> ring
    rw [h4] at h3
    have h5 : (z ^ 2 + 1) / z ≥ 4 := by linarith
    have h6 : z ^ 2 + 1 ≥ 4 * z := by
      have h7 : (z ^ 2 + 1) / z ≥ 4 := by linarith
      apply (le_div_iff₀ (by linarith)).mp at h7
      linarith
    have h7 : z ^ 2 - 4 * z + 1 ≥ 0 := by
      nlinarith
    have h8 : 0 < Real.sqrt 3 := by positivity
    have h9 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    have h10 : 0 < (2 - Real.sqrt 3) := by
      nlinarith [h8, h9, Real.sqrt_nonneg 3, show Real.sqrt 3 < 2 by
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      ]
    by_contra h
    push_neg at h
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), h1, h2, h, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (z - (2 - Real.sqrt 3)), sq_nonneg (z - (2 + Real.sqrt 3))]
  · -- Assume z ≤ 2 - Real.sqrt 3, prove 4 ≤ z + 1 / z
    intro h
    have h1 : 0 < z := hz.1
    have h2 : z < 1 := hz.2
    have h7 : 0 < Real.sqrt 3 := by positivity
    have h8 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    have h10 : z ^ 2 + 1 ≥ 4 * z := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), sq_nonneg (z - (2 - Real.sqrt 3)), sq_nonneg (z - (2 + Real.sqrt 3)), Real.sqrt_nonneg 3, h, h1, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h7, h8]
    have h11 : z + 1 / z ≥ 4 := by
      have h12 : z + 1 / z = (z ^ 2 + 1) / z := by
        field_simp
        <;> ring
      rw [h12]
      apply (le_div_iff₀ (by linarith)).mpr
      nlinarith
    linarith