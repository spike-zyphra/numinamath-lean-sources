import Mathlib

open Real Set

theorem inequalities_291430 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    sqrt (a ^ 2 + b ^ 2) + sqrt (b ^ 2 + c ^ 2) + sqrt (c ^ 2 + a ^ 2) ≥ sqrt 2 := by

  have h1 : sqrt (a ^ 2 + b ^ 2) ≥ Real.sqrt 2 * (a + b) / 2 := by
    have h2 : a ^ 2 + b ^ 2 ≥ ( (a + b) ^ 2 ) / 2 := by
      nlinarith [sq_nonneg (a - b)]
    have h3 : Real.sqrt (a ^ 2 + b ^ 2) ≥ Real.sqrt (( (a + b) ^ 2 ) / 2 ) := Real.sqrt_le_sqrt (by linarith)
    have h4 : Real.sqrt (( (a + b) ^ 2 ) / 2 ) = Real.sqrt 2 * (a + b) / 2 := by
      have h5 : (( (a + b) ^ 2 ) / 2 ) = ( (a + b) ^ 2 ) / 2 := by ring
      rw [h5]
      have h6 : Real.sqrt ( ( (a + b) ^ 2 ) / 2 ) = Real.sqrt ( ( (a + b) ^ 2 ) ) / Real.sqrt (2:ℝ) := by
        field_simp [Real.sqrt_div]
      have h7 : Real.sqrt ( ( (a + b) ^ 2 ) ) = a + b := by
        rw [Real.sqrt_sq]
        linarith [show 0 ≤ a + b by linarith]
      rw [h6, h7]
      field_simp
      <;> ring_nf <;> norm_num
    linarith [h3, h4]

  have h2 : sqrt (b ^ 2 + c ^ 2) ≥ Real.sqrt 2 * (b + c) / 2 := by
    have h3 : b ^ 2 + c ^ 2 ≥ ( (b + c) ^ 2 ) / 2 := by
      nlinarith [sq_nonneg (b - c)]
    have h4 : Real.sqrt (b ^ 2 + c ^ 2) ≥ Real.sqrt (( (b + c) ^ 2 ) / 2 ) := Real.sqrt_le_sqrt (by linarith)
    have h5 : Real.sqrt (( (b + c) ^ 2 ) / 2 ) = Real.sqrt 2 * (b + c) / 2 := by
      have h6 : (( (b + c) ^ 2 ) / 2 ) = ( (b + c) ^ 2 ) / 2 := by ring
      rw [h6]
      have h7 : Real.sqrt ( ( (b + c) ^ 2 ) / 2 ) = Real.sqrt ( ( (b + c) ^ 2 ) ) / Real.sqrt (2:ℝ) := by
        field_simp [Real.sqrt_div]
      have h8 : Real.sqrt ( ( (b + c) ^ 2 ) ) = b + c := by
        rw [Real.sqrt_sq]
        linarith [show 0 ≤ b + c by linarith]
      rw [h7, h8]
      field_simp
      <;> ring_nf <;> norm_num
    linarith [h4, h5]

  have h3 : sqrt (c ^ 2 + a ^ 2) ≥ Real.sqrt 2 * (c + a) / 2 := by
    have h4 : c ^ 2 + a ^ 2 ≥ ( (c + a) ^ 2 ) / 2 := by
      nlinarith [sq_nonneg (c - a)]
    have h5 : Real.sqrt (c ^ 2 + a ^ 2) ≥ Real.sqrt (( (c + a) ^ 2 ) / 2 ) := Real.sqrt_le_sqrt (by linarith)
    have h6 : Real.sqrt (( (c + a) ^ 2 ) / 2 ) = Real.sqrt 2 * (c + a) / 2 := by
      have h7 : (( (c + a) ^ 2 ) / 2 ) = ( (c + a) ^ 2 ) / 2 := by ring
      rw [h7]
      have h8 : Real.sqrt ( ( (c + a) ^ 2 ) / 2 ) = Real.sqrt ( ( (c + a) ^ 2 ) ) / Real.sqrt (2:ℝ) := by
        field_simp [Real.sqrt_div]
      have h9 : Real.sqrt ( ( (c + a) ^ 2 ) ) = c + a := by
        rw [Real.sqrt_sq]
        linarith [show 0 ≤ c + a by linarith]
      rw [h8, h9]
      field_simp
      <;> ring_nf <;> norm_num
    linarith [h5, h6]

  have h4 : sqrt (a ^ 2 + b ^ 2) + sqrt (b ^ 2 + c ^ 2) + sqrt (c ^ 2 + a ^ 2) ≥ Real.sqrt 2 * ( (a + b) + (b + c) + (c + a) ) / 2 := by
    linarith [h1, h2, h3]

  have h5 : (a + b) + (b + c) + (c + a) = 2 * (a + b + c) := by
    ring

  have h6 : Real.sqrt 2 * ( (a + b) + (b + c) + (c + a) ) / 2 = Real.sqrt 2 := by
    rw [h5]
    have h7 : a + b + c = 1 := h
    rw [h7]
    all_goals
      field_simp <;> nlinarith

  rw [h6] at h4
  linarith [h4]