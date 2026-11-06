import Mathlib

theorem algebra_276309 {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : x = (Real.sqrt (a / b) - Real.sqrt (b / a)) / 2) :
    2 * a * Real.sqrt (1 + x^2) / (x + Real.sqrt (1 + x^2)) = a + b := by
  have hab : 0 < a * b := mul_pos ha hb
  have h1 : Real.sqrt (a / b) = a / (Real.sqrt (a * b)) := by
    have h2 : Real.sqrt (a / b) = Real.sqrt a / Real.sqrt b := by
      rw [Real.sqrt_div (by linarith)]
      all_goals norm_num
      all_goals nlinarith
    have h3 : Real.sqrt a / Real.sqrt b = a / (Real.sqrt (a * b)) := by
      have h4 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
        rw [Real.sqrt_mul (by linarith)]
        all_goals nlinarith
      field_simp [h4, hb.ne.symm]
      <;> ring_nf <;> field_simp [hb.ne.symm]
      <;> ring_nf
    rw [h2, h3]
  have h4 : Real.sqrt (b / a) = b / (Real.sqrt (a * b)) := by
    have h5 : Real.sqrt (b / a) = Real.sqrt b / Real.sqrt a := by
      rw [Real.sqrt_div (by linarith)]
      all_goals norm_num
      all_goals nlinarith
    have h6 : Real.sqrt b / Real.sqrt a = b / (Real.sqrt (a * b)) := by
      have h7 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
        rw [Real.sqrt_mul (by linarith)]
        all_goals nlinarith
      field_simp [h7, ha.ne.symm]
      <;> ring_nf <;> field_simp [ha.ne.symm]
      <;> ring_nf
    rw [h5, h6]
  have h5 : x = (a - b) / (2 * Real.sqrt (a * b)) := by
    rw [hx]
    rw [h1, h4]
    field_simp [show 0 < a * b by positivity, ha.ne.symm, hb.ne.symm]
    <;> ring_nf <;> field_simp [show 0 < a * b by positivity, ha.ne.symm, hb.ne.symm]
    <;> ring_nf <;> norm_num
  have h5' : 1 + x^2 = ((a + b)^2) / (4 * (a * b)) := by
    rw [h5]
    have h6 : ((a - b) / (2 * Real.sqrt (a * b)) : ℝ) ^ 2 = ((a - b) ^ 2) / (4 * (a * b)) := by
      have h11 : 0 < Real.sqrt (a * b) := by
        apply Real.sqrt_pos.mpr
        positivity
      have h12 : (Real.sqrt (a * b) : ℝ) ^ 2 = a * b := Real.sq_sqrt (by positivity)
      field_simp [h11, h12]
      <;> ring_nf <;> field_simp [h12]
      <;> ring_nf
    rw [h6]
    have h11 : 0 < a * b := by positivity
    have h12 : (Real.sqrt (a * b) : ℝ) ^ 2 = a * b := Real.sq_sqrt (by positivity)
    field_simp [show a * b ≠ 0 by nlinarith]
    <;> ring_nf <;> nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb]
  have h6' : Real.sqrt (1 + x^2) = (a + b) / (2 * Real.sqrt (a * b)) := by
    rw [h5']
    have h7 : Real.sqrt (((a + b)^2) / (4 * (a * b)) : ℝ) =
        Real.sqrt ((a + b)^2) / Real.sqrt (4 * (a * b)) := by
      field_simp [Real.sqrt_div]
      all_goals positivity
    rw [h7]
    have h8 : Real.sqrt ((a + b)^2 : ℝ) = a + b := by
      rw [Real.sqrt_sq (show 0 ≤ a + b by nlinarith)]
    have h9 : Real.sqrt (4 * (a * b) : ℝ) = 2 * Real.sqrt (a * b) := by
      calc
        Real.sqrt (4 * (a * b) : ℝ)
          = Real.sqrt (4 : ℝ) * Real.sqrt (a * b : ℝ) := by
            rw [Real.sqrt_mul (by positivity)]
            all_goals positivity
        _ = Real.sqrt (2 ^ 2 : ℝ) * Real.sqrt (a * b : ℝ) := by norm_num
        _ = (2 : ℝ) * Real.sqrt (a * b : ℝ) := by
          rw [Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
          all_goals positivity
        _ = (2 * Real.sqrt (a * b) : ℝ) := by ring_nf
    rw [h8, h9]
  have h7' : x + Real.sqrt (1 + x^2) = a / Real.sqrt (a * b) := by
    rw [h6']
    rw [h5]
    field_simp [show 0 < a * b by positivity, ha.ne.symm, hb.ne.symm]
    <;> ring_nf <;> norm_num
    all_goals nlinarith
  have h7'' : 2 * a * Real.sqrt (1 + x^2) = a * (a + b) / Real.sqrt (a * b) := by
    rw [h6']
    field_simp [show 0 < a * b by positivity, ha.ne.symm, hb.ne.symm]
    <;> ring_nf <;> norm_num
  rw [h7', h7'']
  field_simp [show 0 < a * b by positivity, ha.ne.symm, hb.ne.symm]
  <;> ring_nf <;> norm_num
  all_goals nlinarith
  all_goals nlinarith [Real.sqrt_nonneg (a * b)]