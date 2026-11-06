import Mathlib

theorem inequalities_120679 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) ≥ 2 / (1 / a + 1 / b) := by 
  have ha1 : 0 < a := ha
  have hb1 : 0 < b := hb
  have h1 : 1 / a + 1 / b = (a + b) / (a * b) := by
    field_simp
    <;> ring
  have h2 : 2 / (1 / a + 1 / b) = 2 * (a * b) / (a + b) := by
    rw [h1]
    field_simp [(show 0 < a + b from by linarith)]
    <;> ring
  rw [h2]
  have h3 : 0 < a + b := by linarith [ha, hb]
  have h4 : 0 < Real.sqrt (a * b) := by 
    apply Real.sqrt_pos.mpr
    positivity
  have h6 : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt (by positivity)
  have h7 : (2 * (a * b) / (a + b)) ^ 2 ≤ a * b := by
    have h8 : 0 < a + b := h3
    have h9 : (2 * (a * b) / (a + b)) ^ 2 - a * b ≤ 0 := by 
      have h10 : (2 * (a * b) / (a + b)) ^ 2 - a * b = (4 * (a * b) ^ 2 - a * b * (a + b) ^ 2) / ( (a + b) ^ 2 ) := by 
        field_simp 
        <;> ring 
      rw [h10] at *
      apply div_nonpos_of_nonpos_of_nonneg 
      · -- Show $4 * (a * b) ^ 2 - a * b * (a + b) ^ 2 \leq 0$.
        have h11 : 4 * (a * b) ^ 2 - a * b * (a + b) ^ 2 ≤ 0 := by 
          have h14 : 4 * (a * b) ^ 2 - a * b * (a + b) ^ 2 = a * b * (4 * (a * b) - (a + b) ^ 2) := by 
            ring
          rw [h14]
          have h15 : 4 * (a * b) - (a + b) ^ 2 ≤ 0 := by 
            nlinarith [sq_nonneg (a - b)]
          have h17 : a * b > 0 := mul_pos ha hb
          nlinarith
        linarith
      · -- Show $(a + b) ^ 2 \geq 0$.
        positivity
    linarith
  have h14 : Real.sqrt (a * b) ≥ 0 := by positivity
  have h15 : (2 * (a * b) / (a + b) : ℝ) ≥ 0 := by 
    apply div_nonneg 
    positivity 
    linarith 
  nlinarith [h6, Real.sqrt_nonneg (a * b), h7, h14, h15, Real.sq_sqrt (show 0 ≤ a * b by positivity)]