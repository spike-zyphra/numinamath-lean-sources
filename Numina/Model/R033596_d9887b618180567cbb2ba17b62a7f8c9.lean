import Mathlib

theorem algebra_2450 (x : ℝ) (hx : 0 < x ∧ x < 2) :
  Real.sqrt (((x ^ 2 + 4) / (2 * x)) + 2) +
  Real.sqrt (((x ^ 2 + 4) / (2 * x)) - 2) =
  2 / x * Real.sqrt (2 * x) := by
  have hx1 : 0 < x := hx.1
  have hx2 : x < 2 := hx.2
  have h1 : (x ^ 2 + 4 : ℝ) / (2 * x) + 2 = ((x + 2) ^ 2) / (2 * x) := by 
    field_simp
    <;> nlinarith
  have h2 : (x ^ 2 + 4 : ℝ) / (2 * x) - 2 = ((x - 2) ^ 2) / (2 * x) := by 
    field_simp
    <;> nlinarith
  have h3 : Real.sqrt (((x ^ 2 + 4) / (2 * x)) + 2) = (x + 2) / Real.sqrt (2 * x) := by
    rw [h1]
    have h3a : Real.sqrt (((x + 2) ^ 2) / (2 * x)) = Real.sqrt ((x + 2) ^ 2) / Real.sqrt (2 * x) := by
      rw [← Real.sqrt_div]
      positivity
    rw [h3a]
    have h3b : Real.sqrt ((x + 2) ^ 2) = x + 2 := by
      rw [Real.sqrt_sq]
      linarith
    rw [h3b]
    <;> field_simp [Real.sqrt_pos.mpr (show 0 < 2 * x by linarith)]
    all_goals nlinarith
  have h4 : Real.sqrt (((x ^ 2 + 4) / (2 * x)) - 2) = (2 - x) / Real.sqrt (2 * x) := by
    rw [h2]
    have h4a : Real.sqrt (((x - 2) ^ 2) / (2 * x)) = Real.sqrt ((x - 2) ^ 2) / Real.sqrt (2 * x) := by
      rw [← Real.sqrt_div]
      positivity
    rw [h4a]
    have h4b : Real.sqrt ((x - 2) ^ 2) = (2 - x : ℝ) := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_neg]
      linarith
      all_goals linarith
    rw [h4b]
    <;> field_simp [Real.sqrt_pos.mpr (show 0 < 2 * x by linarith)]
    all_goals nlinarith
  rw [h3, h4]
  have h5 : (x + 2 : ℝ) / Real.sqrt (2 * x) + (2 - x) / Real.sqrt (2 * x) =
    4 / Real.sqrt (2 * x) := by
    field_simp
    <;> ring_nf
    <;> norm_num
    <;> nlinarith
    all_goals positivity
  rw [h5]
  have h6 : Real.sqrt (2 * x) > 0 := by
    apply Real.sqrt_pos.mpr
    linarith
  have h7 : x > 0 := by linarith
  have h8 : 4 / Real.sqrt (2 * x) = 2 / x * Real.sqrt (2 * x) := by
    have hx8 : Real.sqrt (2 * x) ^ 2 = 2 * x := Real.sq_sqrt (by linarith)
    have hx_pos : x > 0 := h7
    have h9 : Real.sqrt (2 * x) > 0 := h6
    have hx12 : x * Real.sqrt (2 * x) > 0 := mul_pos h7 h6
    have eq5 : 4 / Real.sqrt (2 * x) = 2 / x * Real.sqrt (2 * x) := by
      have h13 : 4 / Real.sqrt (2 * x) - (2 / x * Real.sqrt (2 * x)) = 0 := by
        have h14 : 4 / Real.sqrt (2 * x) - (2 / x * Real.sqrt (2 * x)) = 
          (4 * x - 2 * (Real.sqrt (2 * x)) ^ 2) / (x * Real.sqrt (2 * x)) := by
          field_simp [show x ≠ 0 by linarith, show Real.sqrt (2 * x) ≠ 0 by 
            by_contra h 
            have h10 : Real.sqrt (2 * x) = 0 := by linarith 
            have h11 : Real.sqrt (2 * x) > 0 := h6 
            linarith 
          ]
          <;> ring_nf 
          <;> norm_num 
          all_goals try { linarith } 
          all_goals positivity
        rw [h14]
        have hx9' : (Real.sqrt (2 * x)) ^ 2 = 2 * x := Real.sq_sqrt (by linarith)
        have h15 : 4 * x - 2 * (Real.sqrt (2 * x)) ^ 2 = 0 := by 
          rw [hx9']
          nlinarith 
        rw [h15]
        norm_num
      linarith 
    linarith 
  linarith [h8]
  <;> positivity
  all_goals positivity
  all_goals positivity
  all_goals positivity
  all_goals positivity
  all_goals positivity
  all_goals positivity
  all_goals positivity