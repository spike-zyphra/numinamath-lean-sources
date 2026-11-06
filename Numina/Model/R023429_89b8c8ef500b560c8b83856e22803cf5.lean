import Mathlib

open Real Set

theorem algebra_229582 :
    IsLeast {z : ℝ | ∃ x y : ℝ, z = 1 / (x + y) ^ 2 + 1 / (x - y) ^ 2 ∧ x ^ 2 + y ^ 2 = 2 ∧ |x| ≠ |y|} 1 := by
  constructor
  · -- Show 1 is in the set
    use (0 : ℝ), Real.sqrt 2
    constructor
    · -- Show expression equals 1
      have h1 : (0 + Real.sqrt 2) ^ 2 = 2 := by 
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h2 : (0 - Real.sqrt 2) ^ 2 = 2 := by 
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      rw [h1, h2]
      field_simp
      <;> linarith 
    constructor
    · -- Show x ^ 2 + y ^ 2 = 2 
      have h3 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      nlinarith
    · -- Show |x| ≠ |y|
      have h4 : Real.sqrt 2 > 0 := by 
        positivity
      norm_num [abs_zero, abs_of_pos h4]
      all_goals linarith 
  · -- Show 1 is the least element 
    intro z h 
    rcases h with ⟨x, y, h_eq, h1, hneq⟩
    have h2 : (x + y) ^ 2 > 0 := by
      by_contra h
      push_neg at h
      have h4 : (x + y) ^ 2 = 0 := by nlinarith [sq_nonneg (x + y)]
      have h6 : x + y = 0 := by nlinarith 
      have h7 : y = -x := by linarith 
      have h8 : x ^ 2 + y ^ 2 = 2 := h1 
      have h9 : x^2 = 1 := by 
        rw [show y = -x by linarith] at h8 
        nlinarith 
      have h10 : x = 1 ∨ x = -1 := by 
        have h9' : x^2 = 1 := h9 
        have : x = 1 ∨ x = -1 := by 
          rw [sq_eq_one_iff] at h9' 
          tauto 
        assumption 
      have hx' : |x| = |y| := by 
        rw [show y = -x by nlinarith]
        rw [abs_neg]
        all_goals try norm_num 
        all_goals try tauto 
        all_goals try linarith 
      exfalso 
      tauto 
    -- Next, showing h2' 
    have h2' : (x - y) ^ 2 > 0 := by 
      by_contra h
      push_neg at h
      have h4 : (x - y) ^ 2 = 0 := by nlinarith [sq_nonneg (x - y)]
      have h5 : x - y = 0 := by nlinarith 
      have h6 : x = y := by linarith 
      have h9 : x ^ 2 + y ^ 2 = 2 := h1 
      have hx' : |x| = |y| := by 
        rw [show y = x by linarith]
        all_goals try norm_num 
        all_goals try tauto 
        all_goals try linarith 
      exfalso 
      tauto 
    -- From here, it's okay
    have h3 : 1 / (x + y) ^ 2 + 1 / (x - y) ^ 2 ≥ (1 : ℝ) := by
      have h4 : (x + y) ^ 2 + (x - y) ^ 2 = 4 := by
        nlinarith [sq_nonneg (x * y), h1]
      have h5 : 1 / (x + y) ^ 2 + 1 / (x - y) ^ 2 - (1 : ℝ) ≥ 0 := by
        have h6 : 1 / (x + y) ^ 2 + 1 / (x - y) ^ 2 - 1 =
            ((x - y) ^ 2 + (x + y) ^ 2 - ( (x + y) ^ 2 * (x - y) ^ 2 ) ) / ( (x + y) ^ 2 * (x - y) ^ 2 ) := by
          field_simp 
          <;> ring 
        rw [h6]
        have h7 : (x + y) ^ 2 * (x - y) ^ 2 > 0 := by
          positivity
        have h8 : ((x - y) ^ 2 + (x + y) ^ 2 - ( (x + y) ^ 2 * (x - y) ^ 2 ) ) ≥ 0 := by
          nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x * y), sq_nonneg ((x + y) - (x - y)), sq_nonneg ((x + y) + (x - y)), sq_nonneg (x - y), sq_nonneg (x + y), h1]
        apply div_nonneg
        · linarith
        · positivity
      linarith
    linarith [h_eq, h3]