import Mathlib

theorem algebra_185050 {b : ℝ} (hb : 0 < b ∧ b ≠ 1) (x : ℝ)
    (hx : x = Real.sqrt b / (1 - Real.sqrt b)) :
    (1 - b) / Real.sqrt b * x^2 - 2 * x + Real.sqrt b = 0 := by
  have h1 : 0 < b := hb.1
  have h2 : b ≠ 1 := hb.2
  -- sqrt(b) is positive since b > 0
  have h3 : 0 < Real.sqrt b := by
    have h5 : Real.sqrt b > 0 := by
      apply Real.sqrt_pos.2
      linarith
    exact h5
  have h4 : Real.sqrt b ≠ 1 := by
    by_contra h
    have h5 : b = 1 := by
      calc
        b = (Real.sqrt b) ^ 2 := by rw [Real.sq_sqrt]; linarith
        _ = 1 ^ 2 := by rw [h]
        _ = 1 := by norm_num
    contradiction
  have h5 : 1 - Real.sqrt b ≠ 0 := by
    intro h
    have h6 : Real.sqrt b = 1 := by linarith
    contradiction
  -- Compute x^2 where x = sqrt(b) / (1 - sqrt(b))
  have hx2 : x^2 = b / (1 - Real.sqrt b)^2 := by 
    rw [hx]
    field_simp [h5]
    <;> nlinarith [Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith)]
  have h6 : (1 - b) / Real.sqrt b * x^2 = (1 - b) * b / (Real.sqrt b * (1 - Real.sqrt b)^2) := by
    rw [hx2]
    field_simp [h5]
    <;> ring
  have h7 : 1 - b = (1 - Real.sqrt b) * (1 + Real.sqrt b) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith)]
  have h8 : (1 - b) / Real.sqrt b * x^2 = ( (1 - Real.sqrt b) * (1 + Real.sqrt b) ) * b / (Real.sqrt b * (1 - Real.sqrt b)^2 ) := by
    rw [h6, h7]
  have h9 : (1 - b) / Real.sqrt b * x^2 = ( b * (1 + Real.sqrt b) ) / ( Real.sqrt b * (1 - Real.sqrt b) ) := by
    rw [h8]
    field_simp [h5]
    <;> ring_nf
    <;> nlinarith [Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith)]
  have h10 : 2 * x = 2 * Real.sqrt b / (1 - Real.sqrt b) := by 
    rw [hx]
    field_simp [h5]
    <;> ring
  have h11 : (1 - b) / Real.sqrt b * x^2 - 2 * x + Real.sqrt b =
    (b * (1 + Real.sqrt b) ) / ( Real.sqrt b * (1 - Real.sqrt b) ) - (2 * Real.sqrt b / (1 - Real.sqrt b)) + Real.sqrt b := by
    rw [h9, h10]
  rw [h11]
  have h12 : Real.sqrt b > 0 := h3
  field_simp [h5, h12]
  <;> nlinarith [Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), sq_nonneg (Real.sqrt b - 1)]