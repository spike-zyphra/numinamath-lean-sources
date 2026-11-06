import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_11926 {f : ℝ → ℝ} (hf : f = λ x => 2 * sin (x / 2)) :
    ¬ (∃ x, deriv f x = -1 / deriv f (5 * π - x)) := by
  intro h
  rcases h with ⟨x, hx⟩
  have hf1 : deriv f x = cos (x / 2) := by
    rw [hf]
    simp [deriv_const_mul, deriv_id', mul_comm]
    all_goals 
      ring_nf <;> field_simp [Real.cos_sq]
      <;> ring_nf <;> norm_num
  have hf2 : deriv f (5 * π - x) = cos ((5 * π - x) / 2) := by
    rw [hf]
    simp [deriv_const_mul, deriv_id', mul_comm]
    all_goals 
      ring_nf <;> field_simp [Real.cos_sq]
      <;> ring_nf <;> norm_num
  rw [hf1] at hx
  rw [hf2] at hx
  have h1 : cos ((5 * π - x) / 2) = sin (x / 2) := by 
    have h2 : (5 * π - x) / 2 = 5 * π / 2 - x / 2 := by 
      linarith 
    rw [h2]
    have h3 : cos (5 * π / 2 - x / 2) = cos (5 * π / 2) * cos (x / 2) + sin (5 * π / 2) * sin (x / 2) := by 
      rw [cos_sub]
    rw [h3]
    have h4 : cos (5 * π / 2) = 0 := by
      have h5 : 5 * π / 2 = 2 * π + π / 2 := by
        linarith [Real.pi_pos]
      rw [h5]
      have h6 : cos (2 * π + π / 2) = cos (π / 2) := by 
        rw [show 2 * π + π / 2 = π / 2 + 2 * π by ring]
        rw [cos_add_two_pi]
      rw [h6]
      norm_num
    have h8 : sin (5 * π / 2) = 1 := by 
      have h9 : 5 * π / 2 = 2 * π + π / 2 := by 
        linarith [Real.pi_pos]
      rw [h9]
      have h10 : sin (2 * π + π / 2) = sin (π / 2) := by 
        rw [show 2 * π + π / 2 = π / 2 + 2 * π by ring]
        rw [sin_add_two_pi]
      rw [h10]
      norm_num
    rw [h4, h8]
    all_goals 
      ring_nf 
  rw [h1] at hx
  have h2 : sin (x / 2) ≠ 0 := by
    by_contra h
    have h3 : sin (x / 2) = 0 := by
      linarith
    have hx1 : cos (x / 2) = 0 := by
      field_simp [h3] at hx
      all_goals 
        nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
    have h4 : cos (x / 2) ^ 2 + sin (x / 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq (x / 2)
    rw [hx1, h3] at h4
    all_goals 
      nlinarith
  have hx2 : cos (x / 2) * sin (x / 2) = -1 := by
    field_simp [h2] at hx
    linarith
  have h3 : cos (x / 2) * sin (x / 2) ≥ -1 / 2 := by
    have h6 : 2 * (cos (x / 2) * sin (x / 2)) = sin x := by
      have h7 : sin x = 2 * sin (x / 2) * cos (x / 2) := by 
        rw [←sin_two_mul]
        ring_nf
      linarith [h7]
    have h7 : sin x ≥ -1 := by 
      linarith [Real.neg_one_le_sin x, Real.sin_le_one x]
    nlinarith [Real.sin_sq_add_cos_sq (x / 2), Real.sin_le_one x, Real.neg_one_le_sin x]
  linarith