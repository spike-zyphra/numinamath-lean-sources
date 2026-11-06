import Mathlib

open Real Set


theorem inequalities_113311 (α β : ℝ) (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2)) :
    cos α * sin (2 * α) * sin (2 * β) ≤ 4 * sqrt 3 / 9 := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with  ⟨h₁₁, h₁₂⟩
  have h2 : 0 < α := by linarith
  have h3 : α < π / 2 := by linarith
  have h4 : 0 < β := by linarith
  have h5 : β < π / 2 := by linarith
  have hsin2β : 0 < sin (2 * β) := by
    apply sin_pos_of_pos_of_lt_pi
    · -- Show 0 < 2 * β
      nlinarith [h4, h5, Real.pi_pos]
    · -- Show 2 * β < Real.pi
      nlinarith [h4, h5, Real.pi_pos]
  have hsin2α : 0 < sin (2 * α) := by
    apply sin_pos_of_pos_of_lt_pi
    · -- Show 0 < 2 * α
      nlinarith [h2, h3, Real.pi_pos]
    · -- Show 2 * α < Real.pi
      nlinarith [h2, h3, Real.pi_pos]
  have hcosα : 0 < cos α := by
    apply cos_pos_of_mem_Ioo
    constructor
    · -- Show 0 - π/2 < α
      linarith [h2, Real.pi_pos]
    · -- Show α < π/2
      linarith [h3, Real.pi_pos]
  have h6 : sin (2 * β) ≤ 1 := by
    have h7 : sin (2 * β) ≤ 1 := by
      apply sin_le_one
    linarith
  have h7 : cos α * sin (2 * α) * sin (2 * β) ≤ cos α * sin (2 * α) := by
    have h8 : sin (2 * β) ≤ 1 := by
      apply sin_le_one
    have h9 : 0 ≤ cos α * sin (2 * α) := by
      positivity
    nlinarith [hsin2β]
  have h8 : cos α * sin (2 * α) ≤ 4 * Real.sqrt 3 / 9 := by
    have h9 : sin (2 * α) = 2 * sin α * cos α := by rw [sin_two_mul]
    rw [h9]
    have h3sin : 0 < sin α := by
      apply sin_pos_of_pos_of_lt_pi
      · -- Show 0 < α
        linarith [h2, Real.pi_pos]
      · -- Show α < Real.pi
        nlinarith [h3, Real.pi_pos]
    have h10 : cos α * (2 * sin α * cos α) ≤ 4 * Real.sqrt 3 / 9 := by
      have h11 : cos α ^ 2 = 1 - sin α ^ 2 := by
        rw [← Real.cos_sq_add_sin_sq α]
        nlinarith
      nlinarith [sq_nonneg (sin α - Real.sqrt 3 / 3), sq_nonneg (cos α ^ 2 - 2 / 3), sq_nonneg (sin α * cos α ^ 2 - Real.sqrt 3 / 9 * 2), 
        sq_nonneg (sin α ^ 2 - 1 / 3), Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sqrt_nonneg 3, 
        mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3), sq_nonneg (sin α - Real.sqrt 3 / 3), sq_nonneg (cos α ^ 2 - 2 / 3)]
    linarith
  have h9 : cos α * sin (2 * α) * sin (2 * β) ≤ 4 * Real.sqrt 3 / 9 := by
    nlinarith [h7, h8, h6]
  nlinarith