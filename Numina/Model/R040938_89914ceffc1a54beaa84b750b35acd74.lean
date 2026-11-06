import Mathlib

theorem algebra_193420 {x y : ℝ} : 
    (x^3 + y^3 = 400) ∧ (x^2 * y + x * y^2 = 200) ↔
    (x = 5 + Real.sqrt 5 ∧ y = 5 - Real.sqrt 5) ∨ (x = 5 - Real.sqrt 5 ∧ y = 5 + Real.sqrt 5) := by
  constructor
  · -- Forward implication: If (x^3 + y^3 = 400) ∧ (x^2 * y + x * y^2 = 200), then (x,y) is either (5+√5,5-√5) or (5-√5,5+√5)
    rintro ⟨h_eq1, h_eq2⟩
    have eq3 : x * y * (x + y) = 200 := by
      have eq4 : x^2 * y + x * y^2 = x * y * (x + y) := by 
        ring 
      linarith [h_eq2, eq4]
    have eq4 : x^3 + y^3 = (x + y)^3 - 3 * (x * y * (x + y)) := by 
      ring 
    have eq5 : (x + y) ^ 3 - 3 * (x * y * (x + y)) = 400 := by 
      linarith [h_eq1, eq4]
    have h5 : (x + y) ^ 3 = 1000 := by
      have eq6 : (x * y * (x + y)) = 200 := by
        linarith [eq3]
      nlinarith
    have h7 : x + y = 10 := by
      have h8 : (x + y) ^ 3 - 1000 = 0 := by
        linarith [h5]
      have h9 : ((x + y) - 10) * ((x + y) ^ 2 + 10 * (x + y) + 100) = 0 := by 
        ring_nf at h8 ⊢ 
        linarith 
      cases' (mul_eq_zero.mp h9) with h10 h11
      · -- Case where x + y - 10 = 0, so x + y = 10
        linarith
      · -- Case where (x + y)^2 + 10*(x + y) + 100 = 0 
        nlinarith [sq_nonneg ((x + y) + 5)]
    have h8 : x * y = 20 := by 
      have eq9 : x * y * (x + y) = 200 := by 
        linarith [eq3]
      rw [show x + y = 10 by linarith [h7]] at eq9 
      linarith 
    have h_eq3 : (x - (5 + Real.sqrt 5)) * (x - (5 - Real.sqrt 5)) = 0 := by 
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (x - 5), sq_nonneg (y - 5)]
    cases' (mul_eq_zero.mp h_eq3) with h_eq4 h_eq5
    · -- First case 
      have h3 : x = 5 + Real.sqrt 5 := by 
        linarith 
      have h4 : y = 5 - Real.sqrt 5 := by 
        nlinarith [Real.sqrt_nonneg 5, h7, h3]
      left 
      constructor
      · exact h3 
      · exact h4 
    · -- Second case 
      have h3 : x = 5 - Real.sqrt 5 := by 
        linarith 
      have h4 : y = 5 + Real.sqrt 5 := by 
        nlinarith [Real.sqrt_nonneg 5, h7, h3]
      right 
      constructor 
      · exact h3 
      · exact h4 
  · -- Backward implication: If (x,y) are either (5+√5,5-√5) or (5-√5,5+√5), then (x^3 + y^3 = 400) ∧ (x^2 * y + x * y^2 = 200).
    rintro (h | h)
    · -- First case 
      rcases h with ⟨hx, hy⟩ 
      constructor 
      · -- First equation 
        rw [hx, hy] 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      · -- Second equation 
        rw [hx, hy] 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    · -- Second case 
      rcases h with ⟨hx, hy⟩ 
      constructor 
      · -- First equation 
        rw [hx, hy] 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      · -- Second equation 
        rw [hx, hy] 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]