import Mathlib

theorem algebra_187768 (x : ℝ) (hx : x ≠ -5) (hx' : x^2 - 25 > 0) :
    Real.logb 2 ((x - 5) / (x + 5)) + Real.logb 2 (x^2 - 25) = 0 ↔ x = 6 := by
  constructor
  · -- Assume the equation holds, prove x = 6
    intro h
    have h1 : x^2 - 25 > 0 := hx'
    have h2 : x + 5 ≠ 0 := by
      intro h3
      apply hx
      linarith
    have h4 : (x - 5) / (x + 5) > 0 := by
      have h5 : (x - 5) * (x + 5) > 0 := by
        nlinarith [h1]
      apply div_pos_iff.mpr
      by_cases h10 : x + 5 > 0
      · -- x + 5 > 0
        left
        constructor
        · -- Show x - 5 > 0
          nlinarith
        · -- Show x + 5 > 0
          assumption
      · -- x + 5 ≤ 0
        push_neg at h10
        right
        constructor
        · -- Show x - 5 < 0
          nlinarith
        · -- Show x + 5 < 0
          by_contra h11
          push_neg at h11
          have : x + 5 = 0 := by linarith
          contradiction
    have h5_log : Real.logb 2 ((x - 5) / (x + 5)) + Real.logb 2 (x^2 - 25) =
      Real.logb 2 (((x - 5) / (x + 5)) * (x^2 - 25)) := by
      have h10_pos1 : (x - 5) / (x + 5) > 0 := h4
      have h11_pos2 : x^2 - 25 > 0 := by linarith [h1]
      have h5 : Real.logb 2 ((x - 5) / (x + 5)) + Real.logb 2 (x^2 - 25) =
          Real.logb 2 (((x - 5) / (x + 5)) * (x^2 - 25)) := by
          rw [← Real.logb_mul (by linarith) (by linarith)]
      linarith
    rw [h5_log] at h
    have h6_pos : ((x - 5) / (x + 5)) * (x^2 - 25) > 0 := by
      apply mul_pos
      · -- Show (x - 5) / (x + 5) > 0
        linarith [h4]
      · -- Show x^2 - 25 > 0
        linarith [h1]
    have h7 : ((x - 5) / (x + 5)) * (x^2 - 25) = 1 := by
      have h8 : Real.logb 2 (((x - 5) / (x + 5)) * (x^2 - 25)) = 0 := h
      have h9 : ((x - 5) / (x + 5)) * (x^2 - 25) = 1 := by
        have h10 : ((x - 5) / (x + 5)) * (x^2 - 25) > 0 := h6_pos
        have h11 : Real.logb 2 (((x - 5) / (x + 5)) * (x^2 - 25)) = 0 := h8
        rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith) ] at h11
        · -- Show the equality
          norm_num at h11 ⊢
          linarith
        all_goals linarith
      assumption
    have h8' : ((x - 5) / (x + 5)) * (x^2 - 25) = (x - 5) ^ 2 := by
      have h9 : x + 5 ≠ 0 := h2
      field_simp [h9]
      <;> nlinarith
    rw [h8'] at h7
    have h14 : (x - 5) ^ 2 = 1 := by
      linarith
    have h15 : x - 5 = 1 ∨ x - 5 = -1 := by
      have h16 : (x - 5) ^ 2 = 1 := h14
      have : x - 5 = 1 ∨ x - 5 = -1 := by
        rw [sq_eq_one_iff] at h16
        tauto
      assumption
    cases h15 with
    | inl h11 =>
      linarith
    | inr h12 =>
      have h17 : x = 4 := by linarith
      nlinarith
  · -- Show x = 6, prove the equation
    intro h
    rw [h]
    have h14 : Real.logb 2 ((6 - 5 : ℝ) / (6 + 5 : ℝ)) + Real.logb 2 ((6 : ℝ) ^ 2 - 25) =
        Real.logb 2 (((6 - 5 : ℝ) / (6 + 5 : ℝ)) * ((6 : ℝ) ^ 2 - 25)) := by
      rw [← Real.logb_mul (by norm_num) (by norm_num)]
    rw [h14]
    have h15 : ((6 - 5 : ℝ) / (6 + 5 : ℝ)) * ((6 : ℝ) ^ 2 - 25) = 1 := by
      norm_num
    rw [h15]
    norm_num [Real.logb_one]