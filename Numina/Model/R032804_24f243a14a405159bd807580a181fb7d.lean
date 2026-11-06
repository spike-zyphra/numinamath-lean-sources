import Mathlib

theorem algebra_16065  :
    IsLeast {k | ∃ x, 0 < x^2 + 1/x^2 ∧ 0 < x - 1 / x ∧ k = (x^2 + 1/x^2) / (x - 1 / x )}  (2 * Real.sqrt 2) := by
  constructor
  · -- First show $2\sqrt{2}$ can be achieved, using $x = \frac{\sqrt{2} + \sqrt{6}}{2}$.
    use (Real.sqrt 2 + Real.sqrt 6)/2
    constructor
    · -- Show $0 < x^2 + \frac{1}{x^2}$.
      have h3 : Real.sqrt 2 > 0 := by positivity
      have h4 : Real.sqrt 6 > 0 := by positivity
      have h7 : ((Real.sqrt 2 + Real.sqrt 6)/2) ^ 2 + 1 / ((Real.sqrt 2 + Real.sqrt 6)/2) ^ 2 = 4 := by
        have h3 : Real.sqrt 2 > 0 := by positivity
        have h4 : Real.sqrt 6 > 0 := by positivity
        field_simp [(show Real.sqrt 2 + Real.sqrt 6 ≠ 0 by positivity)]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - Real.sqrt 6), sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num), sq_pos_of_pos (show (0 : ℝ) < 6 by norm_num)]
      positivity
    constructor
    · -- Show $0 < x - \frac{1}{x}$.
      have h3 : Real.sqrt 2 > 0 := by positivity
      have h4 : Real.sqrt 6 > 0 := by positivity
      have h4' : ((Real.sqrt 2 + Real.sqrt 6)/2) - 1 / ((Real.sqrt 2 + Real.sqrt 6)/2) = Real.sqrt 2 := by 
        have h3 : Real.sqrt 2 > 0 := by positivity
        have h4 : Real.sqrt 6 > 0 := by positivity
        field_simp [(show Real.sqrt 2 + Real.sqrt 6 ≠ 0 by positivity)]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - Real.sqrt 6), sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num), sq_pos_of_pos (show (0 : ℝ) < 6 by norm_num)]
      have h5 : Real.sqrt 2 > 0 := by positivity
      linarith 
    · -- Show $k = \frac{A}{B}$.
      have h3 : Real.sqrt 2 > 0 := by positivity
      have h4 : Real.sqrt 6 > 0 := by positivity
      have h7 : ((Real.sqrt 2 + Real.sqrt 6)/2) ^ 2 + 1 / ((Real.sqrt 2 + Real.sqrt 6)/2) ^ 2 = 4 := by
        have h3 : Real.sqrt 2 > 0 := by positivity
        have h4 : Real.sqrt 6 > 0 := by positivity
        field_simp [(show Real.sqrt 2 + Real.sqrt 6 ≠ 0 by positivity)]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - Real.sqrt 6), sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num), sq_pos_of_pos (show (0 : ℝ) < 6 by norm_num)]
      have h4' : ((Real.sqrt 2 + Real.sqrt 6)/2) - 1 / ((Real.sqrt 2 + Real.sqrt 6)/2) = Real.sqrt 2 := by 
        have h3 : Real.sqrt 2 > 0 := by positivity
        have h4 : Real.sqrt 6 > 0 := by positivity
        field_simp [(show Real.sqrt 2 + Real.sqrt 6 ≠ 0 by positivity)]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - Real.sqrt 6), sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num), sq_pos_of_pos (show (0 : ℝ) < 6 by norm_num)]
      have h6 : (4 / Real.sqrt 2) = 2 * Real.sqrt 2 := by 
        have h3 : Real.sqrt 2 > 0 := by positivity
        field_simp 
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      rw [show ((Real.sqrt 2 + Real.sqrt 6)/2) ^ 2 + 1 / ((Real.sqrt 2 + Real.sqrt 6)/2) ^ 2 = (4 : ℝ) by linarith [h7], show ((Real.sqrt 2 + Real.sqrt 6)/2) - 1 / ((Real.sqrt 2 + Real.sqrt 6)/2) = (Real.sqrt 2 : ℝ) by linarith [h4']]
      rw [h6]
  · -- Show that $2\sqrt{2}$ is minimum.
    intro k hk
    rcases hk with ⟨x, ha, hb, hk⟩
    have h1 : x^2 + 1/x^2 = (x - 1/x)^2 + 2 := by
      field_simp [(show x ≠ 0 by 
        by_contra h
        rw [h] at ha hb
        norm_num at ha hb
      )]
      nlinarith
    have h4 : (x^2 + 1/x^2) / (x - 1/x) ≥ 2 * Real.sqrt 2 := by
      have h5 : (x^2 + 1/x^2) = (x - 1/x)^2 + 2 := h1
      rw [h5]
      have h16 : (x - 1/x) > 0 := hb
      have h10 : ((x - 1/x) ^ 2 + 2) / (x - 1/x) = (x - 1/x) + 2 / (x - 1/x) := by
        field_simp [(show x - 1/x ≠ 0 by linarith)]
        <;> ring
      rw [h10]
      have h7 : (x - 1/x) + 2 / (x - 1/x) ≥ 2 * Real.sqrt 2 := by
        have hb4 : x - 1/x > 0 := hb
        have h18 : (x - 1/x) * (2 / (x - 1/x)) = 2 := by
          field_simp [(show x - 1/x ≠ 0 by linarith)]
        nlinarith [sq_nonneg ((x - 1/x) - Real.sqrt 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      linarith 
    have hk' : k = (x^2 + 1/x^2) / (x - 1/x) := by 
      linarith [hk]
    linarith [hk', h4]