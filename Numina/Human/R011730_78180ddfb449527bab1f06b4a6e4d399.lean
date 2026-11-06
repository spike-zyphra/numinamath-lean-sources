import Mathlib

open Real Set
open scoped Real

theorem inequalities_47525 (a : ℝ) (ha : a ∈ Ioo 0 (π/2)) :
    1 / tan (a/2) > 1 + 1 / tan a := by
  have h1 : 0 < a := ha.left
  have h2 : a < π / 2 := ha.right
  have h3 : 0 < tan (a / 2) := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    · linarith [h1]
    · -- Show a / 2 < π / 2
      linarith [h2, Real.pi_pos]
  have h4 : 0 < tan a := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    · linarith [h1]
    · -- Show a < π / 2 (given)
      linarith [h2]
  have h5 : sin a > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith [h1]
    · linarith [h2, Real.pi_pos]
  have h6 : cos a > 0 := by
    have h7 : a < π / 2 := h2
    have h8 : cos a > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [h1]
      · linarith [h7, Real.pi_pos]
    exact h8
  have h9 : 1 / tan (a / 2) = (1 + cos a) / sin a := by
    have htan : tan (a / 2) = sin a / (1 + cos a) := by
      rw [tan_eq_sin_div_cos]
      have hcos : cos (a / 2) ≠ 0 := by
        have h10 : a / 2 ∈ Ioo (-(π / 2)) (π / 2) := by
          constructor
          · linarith [h1, Real.pi_pos]
          · linarith [h2, Real.pi_pos]
        have h11 : cos (a / 2) > 0 := by
          apply cos_pos_of_mem_Ioo
          exact h10
        linarith
      have hsin : sin (a / 2) > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        · linarith [h1]
        · -- Show a / 2 < π
          linarith [h2, Real.pi_pos]
      have h12 : cos (a / 2) > 0 := by
        have h13 : a / 2 ∈ Ioo (-(π / 2)) (π / 2) := by
          constructor
          · linarith [h1, Real.pi_pos]
          · linarith [h2, Real.pi_pos]
        apply cos_pos_of_mem_Ioo
        exact h13
      have h14 : sin a = 2 * sin (a / 2) * cos (a / 2) := by
        rw [←sin_two_mul (a / 2)]
        ring
      have h15 : 1 + cos a = 2 * cos (a / 2) ^ 2 := by
        have hcos : cos a = 2 * cos (a / 2) ^ 2 - 1 := by
          rw [←cos_two_mul (a / 2)]
          ring
        linarith [hcos]
      field_simp [hcos]
      rw [h14, h15]
      <;> ring
    rw [htan]
    field_simp [show sin a ≠ 0 by nlinarith [h5], show (1 + cos a) ≠ 0 by nlinarith [h6]]
  have h10 : 1 / tan a = cos a / sin a := by
    have htan : tan a = sin a / cos a := by
      rw [tan_eq_sin_div_cos]
    rw [htan]
    field_simp [ne_of_gt h6]
  rw [h9]
  have h11 : 1 + 1 / tan a = 1 + cos a / sin a := by
    rw [h10]
  rw [h11]
  have h12 : sin a < 1 := by
    have h13 : a < π / 2 := h2
    have h14 : sin a < 1 := by
      have h15 : sin a < sin (π / 2) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [h1, h13, Real.pi_pos]
      have h16 : sin (π / 2) = 1 := Real.sin_pi_div_two
      linarith [h16]
    exact h14
  have h13 : (1 + cos a) / sin a > 1 + cos a / sin a := by
    have h14 : sin a > 0 := h5
    have h15 : 1 + cos a / sin a < (1 + cos a) / sin a := by 
      have h17 : (1 + cos a) / sin a - (1 + cos a / sin a) > 0 := by
        have h18 : (1 + cos a) / sin a - (1 + cos a / sin a) = (1 - sin a) / sin a := by 
          field_simp [h14]
          <;> ring
        rw [h18]
        apply div_pos
        · linarith [h12]
        · linarith [h5]
      linarith [h17]
    linarith [h15]
  linarith [h13]