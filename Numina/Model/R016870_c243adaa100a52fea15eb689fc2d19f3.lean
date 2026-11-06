import Mathlib

theorem algebra_296964 {α β : ℝ} (h : α ≠ β) (h1 : α^2 - 7 * α + 8 = 0) (h2 : β^2 - 7 * β + 8 = 0)
    (h3 : α > β) : (2 / α) + 3 * β^2 = (403 - 85 * Real.sqrt 17) / 8 := by
  have h4 : α ≠ 0 := by 
    by_contra hα 
    rw [hα] at h1 
    nlinarith 
  have h5 : β ≠ 0 := by 
    by_contra hβ 
    rw [hβ] at h2 
    nlinarith 
  have h6 : α - β > 0 := by 
    linarith 
  have h7 : α ^ 2 - β ^ 2 = 7 * (α - β) := by 
    nlinarith 
  have h9 : α + β = 7 := by
    have hne : α - β ≠ 0 := by
      intro h'
      apply h
      linarith
    apply (mul_left_inj' hne).mp
    linarith
  -- Calculate the product of roots using Vieta's formula
  have h10 : α * β = 8 := by 
    nlinarith [sq_pos_of_ne_zero (show α - β ≠ 0 by 
      intro h'
      apply h
      linarith 
    ), sq_nonneg (α - β), sq_nonneg (α + β - 7)]
  have h13 : (α - β) ^ 2 > 0 := by
    have h14 : α - β > 0 := h6 
    nlinarith 
  have h14 : α^2 = 7 * α - 8 := by linarith 
  have h15 : β^2 = 7 * β - 8 := by linarith 
  have h16 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h17 : Real.sqrt 17 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have h18 : (α - ( (7 + Real.sqrt 17) / 2 )) * (α - ( (7 - Real.sqrt 17) / 2 )) = 0 := by 
    nlinarith [ Real.sqrt_pos.mpr (show (17 : ℝ) > 0 by norm_num ), sq_nonneg ( α - 7 / 2 ), sq_nonneg ( Real.sqrt 17 ), Real.sq_sqrt ( show (0 : ℝ) ≤ (17 : ℝ) by norm_num ) ]
  cases' (mul_eq_zero.mp h18) with h20 h21 
  · -- Case where α is the positive root.
    have h22 : α = ( (7 + Real.sqrt 17) / 2 ) := by linarith 
    have h23 : β = ( (7 - Real.sqrt 17) / 2 ) := by 
      nlinarith [ h2, Real.sqrt_pos.mpr ( show (17 : ℝ) > 0 by norm_num ), sq_nonneg ( β - 7 / 2 ), Real.sq_sqrt ( show (0 : ℝ) ≤ (17 : ℝ) by norm_num ), sq_nonneg ( Real.sqrt 17 ) ]
    rw [h22, h23] 
    field_simp
    ring_nf 
    <;> nlinarith [ Real.sqrt_pos.mpr ( show (17 : ℝ) > 0 by norm_num ), Real.sq_sqrt ( show (0 : ℝ) ≤ (17 : ℝ) by norm_num ) ]
  · -- Case where α is the negative root.
    exfalso 
    nlinarith [ sq_nonneg ( α - β ), h3, Real.sqrt_pos.mpr ( show (17 : ℝ) > 0 by norm_num ), sq_nonneg ( Real.sqrt 17 ), Real.sq_sqrt ( show (0 : ℝ) ≤ (17 : ℝ) by norm_num ) ]