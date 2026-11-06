import Mathlib

open Real Set
open scoped Real

theorem calculus_22430 (A : Real) (hA : 0 < A ∧ A < π / 2) (h : cos (41 * π / 180) + sin (41 * π / 180) = sqrt 2 * sin A) :
    A = 86 * π / 180 := by
  have h1 : cos (41 * π / 180) + sin (41 * π / 180) = Real.sqrt 2 * sin (86 * π / 180) := by
    have h7 : 86 * π / 180 = 41 * π / 180 + π / 4 := by
      linarith [pi_pos]
    have h8 : sin (86 * π / 180) = sin (41 * π / 180 + π / 4) := by
      rw [h7]
    have h9 : sin (41 * π / 180 + π / 4) = sin (41 * π / 180) * cos (π / 4) + cos (41 * π / 180) * sin (π / 4) := by 
      rw [sin_add]
    have h10 : cos (π / 4) = Real.sqrt 2 / 2 := by 
      rw [cos_pi_div_four]
    have h11 : sin (π / 4) = Real.sqrt 2 / 2 := by 
      rw [sin_pi_div_four]
    have h12 : Real.sqrt 2 * sin (86 * π / 180) = cos (41 * π / 180) + sin (41 * π / 180) := by 
      rw [h8, h9, h10, h11]
      have eq1 : Real.sqrt 2 * (sin (41 * π / 180) * (Real.sqrt 2 / 2) + cos (41 * π / 180) * (Real.sqrt 2 / 2)) = cos (41 * π / 180) + sin (41 * π / 180) := by
        have h14 : Real.sqrt 2 * (sin (41 * π / 180) * (Real.sqrt 2 / 2) + cos (41 * π / 180) * (Real.sqrt 2 / 2)) = (Real.sqrt 2 * Real.sqrt 2 / 2) * (sin (41 * π / 180) + cos (41 * π / 180)) := by ring
        have h15 : Real.sqrt 2 * Real.sqrt 2 = 2 := by 
          calc 
            Real.sqrt 2 * Real.sqrt 2 = (Real.sqrt 2) ^ 2 := by ring
            _ = 2 := by 
              rw [Real.sq_sqrt]
              all_goals norm_num
        rw [h14, h15]
        <;> ring_nf <;> nlinarith 
      linarith [eq1]
    linarith
  have h2 : Real.sqrt 2 * sin (86 * π / 180) = Real.sqrt 2 * sin A := by
    linarith [h1, h]
  have h8 : sin (86 * π / 180) = sin A := by
    have h9 : Real.sqrt 2 ≠ 0 := by 
      positivity
    have h10 : sin (86 * π / 180) = sin A := by
      apply (mul_left_inj' h9).mp
      linarith [h2]
    linarith 
  have h13 : 86 * π / 180 = A := by
    have h9 : 0 < 86 * π / 180 := by
      nlinarith [pi_pos]
    have h10 : 86 * π / 180 < Real.pi / 2 := by
      nlinarith [pi_gt_three]
    have h11 : 0 < A := hA.1
    have h12 : A < Real.pi / 2 := hA.2
    have h14 : sin (86 * π / 180) = sin A := h8
    have h15 : 86 * π / 180 > 0 := h9
    have h16 : 86 * π / 180 < Real.pi := by
      nlinarith [pi_gt_three]
    have h17 : A > 0 := h11
    have h18 : A < Real.pi := by
      nlinarith [pi_gt_three, h12]
    by_cases h22 : 86 * π / 180 < A
    · -- If 86 * π / 180 < A
      have h23 : sin (86 * π / 180) < sin A := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [pi_pos, h9, h10, h22, h11, h12]
      linarith [h14, h23]
    by_cases h24 : 86 * π / 180 > A
    · -- If 86 * π / 180 > A
      have h25 : sin (86 * π / 180) > sin A := by 
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [pi_pos, h9, h10, h24, h11, h12]
      linarith [h14, h25]
    linarith 
  linarith [h13]