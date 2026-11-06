import Mathlib

open Real Set
open scoped Real

theorem algebra_324757 {α : Real} (hα : α ∈ Ioo 0 (π / 2)) :
    (sin α ^ 4 + cos α ^ 4) / (sqrt (sin α ^ 4 + cos α ^ 4)) < (sin α ^ 4 + cos α ^ 4) / (sin α ^ 6 + cos α ^ 6) ∧
    (sin α ^ 4 + cos α ^ 4) / (sin α ^ 6 + cos α ^ 6) < (sqrt (sin α ^ 4 + cos α ^ 4)) / (sin α ^ 6 + cos α ^ 6) := by
  rcases hα with ⟨h1, h2⟩
  have h3 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [h1, h2, Real.pi_pos]
  have h4 : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [h1, h2, Real.pi_pos]
  have h5 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h6 : sin α ^ 4 + cos α ^ 4 > 0 := by
    have h7 : sin α ^ 4 > 0 := by positivity
    have h8 : cos α ^ 4 > 0 := by positivity
    nlinarith
  have h7 : sin α ^ 6 + cos α ^ 6 > 0 := by
    have h8 : sin α ^ 6 > 0 := by positivity
    have h9 : cos α ^ 6 > 0 := by positivity
    nlinarith
  have h9 : sin α ^ 4 + cos α ^ 4 = 1 - 2 * (sin α ^ 2 * cos α ^ 2) := by
    have h8 : sin α ^ 4 + cos α ^ 4 = (sin α ^ 2 + cos α ^ 2) ^ 2 - 2 * (sin α ^ 2 * cos α ^ 2) := by ring
    rw [h5] at h8
    nlinarith
  have h10 : sin α ^ 6 + cos α ^ 6 = 1 - 3 * (sin α ^ 2 * cos α ^ 2) := by
    have h7' : sin α ^ 6 + cos α ^ 6 = (sin α ^ 2 + cos α ^ 2) ^ 3 - 3 * (sin α ^ 2 + cos α ^ 2) * (sin α ^ 2 * cos α ^ 2) := by ring
    rw [h5] at h7'
    nlinarith
  have h8' : 0 < sin α ^ 2 * cos α ^ 2 := by
    nlinarith [h3, h4, mul_pos h3 h4]
  have h11 : (sin α ^ 4 + cos α ^ 4) / (sqrt (sin α ^ 4 + cos α ^ 4)) = sqrt (sin α ^ 4 + cos α ^ 4) := by
    have h12 : sqrt (sin α ^ 4 + cos α ^ 4) > 0 := by positivity
    field_simp [Real.sqrt_nonneg (sin α ^ 4 + cos α ^ 4)]
  have h13 : sqrt (sin α ^ 4 + cos α ^ 4) < (sin α ^ 4 + cos α ^ 4) / (sin α ^ 6 + cos α ^ 6) := by
    have h14 : sin α ^ 4 + cos α ^ 4 > sin α ^ 6 + cos α ^ 6 := by
      have h17 : sin α ^ 6 + cos α ^ 6 = 1 - 3 * (sin α ^ 2 * cos α ^ 2) := h10
      have h18 : sin α ^ 4 + cos α ^ 4 = 1 - 2 * (sin α ^ 2 * cos α ^ 2) := h9
      nlinarith [h8', show sin α ^ 2 * cos α ^ 2 > 0 by linarith]
    have h15 : sqrt (sin α ^ 4 + cos α ^ 4) < 1 := by
      have h16 : sin α ^ 4 + cos α ^ 4 < 1 := by
        have h17 : sin α ^ 4 + cos α ^ 4 = 1 - 2 * (sin α ^ 2 * cos α ^ 2) := h9
        nlinarith [h8']
      have h17 : sqrt (sin α ^ 4 + cos α ^ 4) < sqrt ((1 : ℝ)) := by
        apply Real.sqrt_lt_sqrt
        nlinarith [show sin α ^ 4 + cos α ^ 4 ≥ 0 by positivity]
        linarith
      rw [show sqrt (1 : ℝ) = (1 : ℝ) by rw [Real.sqrt_one]] at h17
      linarith
    have h16 : (sin α ^ 4 + cos α ^ 4) / (sin α ^ 6 + cos α ^ 6) > 1 := by
      have h17 : sin α ^ 4 + cos α ^ 4 > sin α ^ 6 + cos α ^ 6 := h14
      have h18 : sin α ^ 6 + cos α ^ 6 > 0 := h7
      apply (lt_div_iff' (by linarith)).mpr
      nlinarith
    nlinarith [h15, h16]
  have h18 : (sin α ^ 4 + cos α ^ 4) / (sin α ^ 6 + cos α ^ 6) < (sqrt (sin α ^ 4 + cos α ^ 4)) / (sin α ^ 6 + cos α ^ 6) := by
    have h19 : sin α ^ 4 + cos α ^ 4 < sqrt (sin α ^ 4 + cos α ^ 4) := by
      have h20 : sin α ^ 4 + cos α ^ 4 < 1 := by
        have h17 : sin α ^ 4 + cos α ^ 4 = 1 - 2 * (sin α ^ 2 * cos α ^ 2) := h9
        nlinarith [h8']
      have h21 : sin α ^ 4 + cos α ^ 4 > 0 := by positivity
      have h22 : sqrt (sin α ^ 4 + cos α ^ 4) > sin α ^ 4 + cos α ^ 4 := by
        nlinarith [Real.sqrt_nonneg (sin α ^ 4 + cos α ^ 4), Real.sq_sqrt (show sin α ^ 4 + cos α ^ 4 ≥ 0 by positivity)]
      linarith
    have h21 : (sin α ^ 4 + cos α ^ 4) < sqrt (sin α ^ 4 + cos α ^ 4) := h19
    apply (div_lt_div_right (by positivity)).mpr
    linarith
  constructor
  · -- First inequality
    rw [h11]
    linarith [h13]
  · -- Second inequality
    exact h18