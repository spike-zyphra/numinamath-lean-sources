import Mathlib

open Real Set
open scoped BigOperators

/- If the real numbers $x$, $y$ satisfy ${{x}^{2}}+{{y}^{2}}=1$, then the minimum value of $\frac{2xy}{x+y-1}$ is ___          ___. -/
theorem algebra_10706 :
  IsLeast {z : ℝ | ∃ x y, z = 2*x*y / (x + y - 1) ∧ x^2 + y^2 = 1} (1 - sqrt 2) := by
  constructor 
  · -- Show that $1 - \sqrt{2}$ belongs to the set
    use (-sqrt 2 / 2), (-sqrt 2 / 2) 
    constructor 
    · -- Show that $1 - \sqrt{2}$ is achievable
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have h2 : Real.sqrt 2 > 0 := by positivity
      have h3 : (-sqrt 2 / 2 : ℝ) + (-sqrt 2 / 2 : ℝ) - 1 ≠ 0 := by 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
      have hx : 2 * (-sqrt 2 / 2 : ℝ) * (-sqrt 2 / 2 : ℝ) / ((-sqrt 2 / 2 : ℝ) + (-sqrt 2 / 2 : ℝ) - 1 : ℝ) = 1 - sqrt 2 := by
        have hx' : (-sqrt 2 / 2 : ℝ) + (-sqrt 2 / 2 : ℝ) - 1 = -sqrt 2 - 1 := by 
          ring_nf 
          <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
        have eq' : 2 * (-sqrt 2 / 2 : ℝ) * (-sqrt 2 / 2 : ℝ) = 1 := by 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
        rw [hx', eq']
        have denom_nonzero : (-sqrt 2 - 1 : ℝ) ≠ 0 := by
          nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        field_simp [denom_nonzero]
        <;> ring_nf <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
        all_goals linarith 
      linarith [hx]
    · -- Show that $x^2 + y^2 = 1$
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith 
  · -- Show that $1 - \sqrt{2}$ is the least 
    intro z hz
    rcases hz with ⟨x, y, h_eq, h1⟩
    by_cases h2 : x + y - 1 = 0 
    · -- When x + y - 1 = 0, then the expression is defined as 0
      have h_eq' : 2 * x * y / (x + y - 1) = 0 := by 
        rw [h2]
        norm_num 
        <;> linarith 
        all_goals linarith 
      rw [h_eq'] at h_eq 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    · -- When x + y - 1 ≠ 0, then the expression is defined 
      have h2 : x + y - 1 ≠ 0 := h2 
      have h3 : 2 * x * y = (x + y) ^ 2 - 1 := by nlinarith 
      have hx : 2 * x * y / (x + y - 1) = x + y + 1 := by 
        have h4 : 2 * x * y = (x + y) ^ 2 - 1 := by nlinarith 
        have h5 : 2 * x * y / (x + y - 1) = ((x + y) ^ 2 - 1) / (x + y - 1 : ℝ) := by 
          rw [show 2 * x * y = (x + y) ^ 2 - 1 by nlinarith]
          all_goals linarith 
        have h8 : ((x + y : ℝ) ^ 2 - 1 : ℝ) = (x + y - 1) * (x + y + 1 : ℝ) := by 
          nlinarith 
        rw [h8] at h5 
        rw [h5] 
        field_simp [h2] 
        <;> ring 
        all_goals linarith 
      have hx' : (2 * x * y / (x + y - 1) ) = x + y + 1 := hx 
      rw [hx'] at h_eq 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y + Real.sqrt 2), sq_nonneg (x - y), sq_nonneg (x + y - Real.sqrt 2), Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]