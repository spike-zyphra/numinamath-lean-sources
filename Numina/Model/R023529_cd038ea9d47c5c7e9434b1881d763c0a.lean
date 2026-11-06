import Mathlib

theorem algebra_271409 : (2 + 2 * Complex.I)^4 / (1 - Real.sqrt 3 * Complex.I)^5 = -1 + Real.sqrt 3 * Complex.I := by
  have h1 : (2 + 2 * Complex.I : ℂ) ^ 4 = -64 := by
    simp [pow_succ, Complex.ext_iff, Complex.I_mul_I]
    norm_num
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : (1 - Real.sqrt 3 * Complex.I : ℂ) ^ 5 = 16 + 16 * Real.sqrt 3 * Complex.I := by
    have h1 : (1 - Real.sqrt 3 * Complex.I : ℂ) ^ 2 = -2 - 2 * Real.sqrt 3 * Complex.I := by
      simp [pow_two, Complex.ext_iff, Complex.I_mul_I, mul_add, mul_comm, mul_assoc]
      ring_nf
      <;> norm_num
      <;> ring_nf <;> norm_num
      <;> ring_nf <;> norm_num
      <;> ring_nf <;> norm_num
    have h2 : (1 - Real.sqrt 3 * Complex.I : ℂ) ^ 3 = -8 := by
      calc
        (1 - Real.sqrt 3 * Complex.I : ℂ) ^ 3
          = ((1 - Real.sqrt 3 * Complex.I : ℂ) ^ 2) * (1 - Real.sqrt 3 * Complex.I) := by ring
        _ = (-2 - 2 * Real.sqrt 3 * Complex.I) * (1 - Real.sqrt 3 * Complex.I) := by rw [h1]
        _ = -8 := by
          simp [Complex.ext_iff, Complex.I_mul_I, mul_add, mul_comm, mul_assoc]
          ring_nf
          <;> norm_num
          <;> ring_nf <;> norm_num
          <;> nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < (3: ℝ) by norm_num : (0: ℝ) < (3: ℝ)), Real.sq_sqrt (show (0: ℝ) ≤ 3 by norm_num : (0: ℝ) ≤ (3: ℝ)), Real.sqrt_pos.mpr (show (0: ℝ) < (3: ℝ) by norm_num : (0: ℝ) < (3: ℝ))]
    calc
      (1 - Real.sqrt 3 * Complex.I : ℂ) ^ 5
          = ((1 - Real.sqrt 3 * Complex.I : ℂ) ^ 3) * ((1 - Real.sqrt 3 * Complex.I : ℂ) ^ 2) := by ring
      _ = (-8 : ℂ) * ((1 - Real.sqrt 3 * Complex.I : ℂ) ^ 2) := by rw [h2]
      _ = (-8 : ℂ) * (-2 - 2 * Real.sqrt 3 * Complex.I) := by rw [h1]
      _ = 16 + 16 * Real.sqrt 3 * Complex.I := by
        simp [Complex.ext_iff, Complex.I_mul_I, mul_add, mul_comm, mul_assoc]
        ring_nf
        <;> norm_num
        <;> nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < (3: ℝ) by norm_num : (0: ℝ) < (3: ℝ)), Real.sq_sqrt (show (0: ℝ) ≤ 3 by norm_num : (0: ℝ) ≤ (3: ℝ)), Real.sqrt_pos.mpr (show (0: ℝ) < (3: ℝ) by norm_num : (0: ℝ) < (3: ℝ))]
  rw [h1, h2]
  field_simp [Complex.ext_iff, Complex.I_mul_I, mul_add, mul_comm, mul_assoc, pow_two]
  <;> ring_nf
  <;> norm_num
  <;> nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < (3: ℝ) by norm_num : (0: ℝ) < (3: ℝ)), Real.sq_sqrt (show (0: ℝ) ≤ 3 by norm_num : (0: ℝ) ≤ (3: ℝ)), Real.sqrt_pos.mpr (show (0: ℝ) < (3: ℝ) by norm_num : (0: ℝ) < (3: ℝ))]