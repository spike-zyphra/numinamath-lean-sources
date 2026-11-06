import Mathlib

theorem algebra_170778 (h : ℝ) (g : ℝ) (h₀ : h = 20) (g₀ : g = 10) :
    ∃ t, (h / t) = √(2 * g * t) := by
  use (20 : ℝ) ^ (1 / 3 : ℝ)
  rw [h₀, g₀]
  have h1 : (20 : ℝ) / ((20 : ℝ) ^ (1 / 3 : ℝ)) = (20 : ℝ) ^ (2 / 3 : ℝ) := by
    have h2 : (20 : ℝ) ^ (2 / 3 : ℝ) = (20 : ℝ) / ((20 : ℝ) ^ (1 / 3 : ℝ)) := by
      have h3 : (20 : ℝ) ^ (2 / 3 : ℝ) = ((20 : ℝ) ^ (1 : ℝ)) * ((20 : ℝ) ^ (-1 / 3 : ℝ)) := by 
        rw [← Real.rpow_add]
        norm_num
        all_goals norm_num
      rw [h3]
      have h4 : (20 : ℝ) ^ (-1 / 3 : ℝ) = ((20 : ℝ) ^ (1 / 3 : ℝ))⁻¹ := by 
        rw [← Real.rpow_neg]
        norm_num
        all_goals norm_num
      rw [h4]
      field_simp
      <;> norm_num
    linarith [h2]
  have h2 : √(2 * (10 : ℝ) * ((20 : ℝ) ^ (1 / 3 : ℝ)) ) = (20 : ℝ) ^ (2 / 3 : ℝ) := by
    have h3 : (2 * (10 : ℝ) * ((20 : ℝ) ^ (1 / 3 : ℝ)) ) = ( (20 : ℝ) ^ (4 / 3 : ℝ) ) := by
      have h4 : (2 * (10 : ℝ) * ((20 : ℝ) ^ (1 / 3 : ℝ)) ) = (20 : ℝ) * ( (20 : ℝ) ^ (1 / 3 : ℝ) ) := by ring
      rw [h4]
      have h5 : (20 : ℝ) * ( (20 : ℝ) ^ (1 / 3 : ℝ) ) = (20 : ℝ) ^ (4 / 3 : ℝ) := by
        have h6 : (20 : ℝ) ^ (4 / 3 : ℝ) = (20 : ℝ) ^ (1 : ℝ) * (20 : ℝ) ^ (1 / 3 : ℝ) := by 
          rw [← Real.rpow_add]
          norm_num
          all_goals norm_num
        rw [h6]
        norm_num
        <;> norm_num
      rw [h5]
    have h4 : √((20 : ℝ) ^ (4 / 3 : ℝ)) = ((20 : ℝ) ^ (4 / 3 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    have h5 : ((20 : ℝ) ^ (4 / 3 : ℝ)) ^ (1 / 2 : ℝ) = (20 : ℝ) ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    rw [h3]
    rw [h4, h5]
  rw [h1, h2]