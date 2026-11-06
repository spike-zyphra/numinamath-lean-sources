import Mathlib

theorem algebra_319313 {α β : ℝ} (h₁ : α^2-7*α+8=0) (h₂ : β^2-7*β+8=0) (h₃ : α>β) :
    2/α+3*β^2=1/8*(403-85*Real.sqrt 17) := by
  have ha1 : α ≠ 0 := by
    by_contra h
    rw [h] at h₁
    nlinarith
  have hb1 : β ≠ 0 := by
    by_contra h
    rw [h] at h₂
    nlinarith
  have h7 : α + β = 7 := by
    have eq4 : α^2 - β^2 - 7 * α + 7 * β = 0 := by linarith [h₁, h₂]
    have eq5 : (α - β) * (α + β) - 7 * (α - β) = 0 := by linarith
    have eq6 : (α - β) * (α + β - 7) = 0 := by linarith
    cases' (mul_eq_zero.mp eq6) with eq7 eq8
    · -- α - β = 0, which contradicts with α > β
      exfalso
      have ha_eq : α = β := by linarith
      have ha_eq2 : ¬(α > β) := by nlinarith
      contradiction 
    · -- α + β - 7 = 0
      linarith

  have h700 : 2/α = (7 - α)/4 := by
    have h60 : 1/α = (7 - α)/8 := by
      have h60 : α ≠ 0 := ha1
      field_simp
      nlinarith
    have h61 : 1/α = (7 - α)/8 := h60
    calc 
      2/α = 2 * (1/α) := by ring
      _ = 2 * ((7 - α)/8) := by rw [h61]
      _ = (7 - α)/4 := by ring_nf
  
  have h71 : β^2 = 7 * β - 8 := by 
    nlinarith [h₂]

  have h81 : 3 * β^2 = 21 * β - 24 := by
    nlinarith [h71]

  have h7400 : 2/α + 3 * β^2 = (7 - α)/4 + (21 * β - 24) := by 
    linarith [h700, h81]
  
  -- Solving the quadratic to get explicit expressions
  have h99 : α = (7 + Real.sqrt 17)/2 := by
    have h40 : α^2 - 7 * α + 8 = 0 := h₁
    have h41 : (α - (7 + Real.sqrt 17)/2) * (α - (7 - Real.sqrt 17)/2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sqrt_nonneg (17 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h41) with h42 h43
    · -- α = (7 + Real.sqrt 17)/2
      linarith
    · -- α = (7 - Real.sqrt 17)/2
      -- which would be less than β
      have h42 : α = (7 - Real.sqrt 17)/2 := by linarith
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sqrt_nonneg (17 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
  
  have h100 : β = (7 - Real.sqrt 17)/2 := by
    have h40 : β^2 - 7 * β + 8 = 0 := h₂
    have h41 : (β - (7 + Real.sqrt 17)/2) * (β - (7 - Real.sqrt 17)/2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sqrt_nonneg (17 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h41) with h42 h43
    · -- β = (7 + Real.sqrt 17)/2
      -- This would be greater than α, which contradicts h₃
      exfalso
      have ha2 : α < β := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sqrt_nonneg (17 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
      linarith
    · -- β = (7 - Real.sqrt 17)/2
      linarith
  
  rw [h7400, h99, h100]
  -- Simplify the final expression
  have sqrt_pos : 0 < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
  have sqrt_pos_nonneg : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg 17 
  have sqrt_suspect : (Real.sqrt 17 : ℝ) ^ 2 = 17 := Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)
  field_simp
  nlinarith