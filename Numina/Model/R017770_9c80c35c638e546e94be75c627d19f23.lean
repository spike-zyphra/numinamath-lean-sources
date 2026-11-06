import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_294834 {f g : ℝ → ℝ}
  (hfg : ∀ x, f (g x) = sin (2 * x))
  (hg : ∀ x, g x = tan (x / 2)) :
  f (sqrt 2 / 2) = 4 * sqrt 2 / 9 := by 
  have h5 : f (g (2 * (Real.arctan (sqrt 2 / 2)))) = sin (2 * (2 * (Real.arctan (sqrt 2 / 2)))) := hfg (2 * (Real.arctan (sqrt 2 / 2)))
  have h3 : g (2 * (Real.arctan (sqrt 2 / 2))) = sqrt 2 / 2 := by 
    rw [hg]
    have h4 : tan ( (2 * (Real.arctan (sqrt 2 / 2)) ) / 2 ) = sqrt 2 / 2 := by 
      have h5 : (2 * (Real.arctan (sqrt 2 / 2)) ) / 2 = Real.arctan (sqrt 2 / 2) := by ring_nf
      rw [h5]
      rw [Real.tan_arctan]
    simpa using h4 
  have h8 : sin (2 * (2 * (Real.arctan (sqrt 2 / 2)))) = 4 * sqrt 2 / 9 := by
    have h6 : sin (2 * (2 * (Real.arctan (sqrt 2 / 2)))) = 2 * sin (2 * (Real.arctan (sqrt 2 / 2))) * cos (2 * (Real.arctan (sqrt 2 / 2)) ) := by
      rw [show 2 * (2 * (Real.arctan (sqrt 2 / 2))) = 2 * (2 * (Real.arctan (sqrt 2 / 2))) by ring_nf]
      rw [sin_two_mul]
      all_goals ring_nf
    have h7 : sin (2 * (Real.arctan (sqrt 2 / 2))) = 2 * sqrt 2 / 3 := by 
      have h7 : sin (2 * (Real.arctan (sqrt 2 / 2))) = 2 * (sqrt 2 / 2) / (1 + (sqrt 2 / 2)^2) := by
        rw [sin_two_mul, sin_arctan, cos_arctan]
        field_simp
        <;> ring_nf <;> norm_num
      rw [h7]
      have h8 : (sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      field_simp [h8]
      <;> ring_nf <;> norm_num [h8]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h9 : cos (2 * (Real.arctan (sqrt 2 / 2)) ) = 1 / 3 := by
      have h9 : cos (2 * (Real.arctan (sqrt 2 / 2))) = (1 - (sqrt 2 / 2)^2) / (1 + (sqrt 2 / 2)^2) := by
        rw [cos_two_mul, cos_arctan]
        field_simp
        <;> ring_nf <;> norm_num
      rw [h9]
      have h8 : (sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      field_simp [h8]
      <;> ring_nf <;> norm_num [h8]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h6, h7, h9]
    <;> field_simp <;> ring_nf <;> norm_num 
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  rw [show f (sqrt 2 / 2) = f (g (2 * (Real.arctan (sqrt 2 / 2)))) by 
    rw [h3] 
  ] 
  rw [h5, h8]
  all_goals try tauto 
  all_goals try ring_nf <;> norm_num 
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]