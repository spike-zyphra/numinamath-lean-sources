import Mathlib

open Real

theorem calculus_13266 : (sin (10 * π / 180) + sin (20 * π / 180)) / (cos (10 * π / 180) + cos (20 * π / 180)) = tan (15 * π / 180) := by
  have h1 : sin (10 * π / 180) + sin (20 * π / 180) = 2 * sin (15 * π / 180) * cos (5 * π / 180) := by
    rw [show 10 * π / 180 = 15 * π / 180 - 5 * π / 180 by ring]
    rw [show 20 * π / 180 = 15 * π / 180 + 5 * π / 180 by ring]
    rw [sin_add, sin_sub]
    ring

  have h2 : cos (10 * π / 180) + cos (20 * π / 180) = 2 * cos (15 * π / 180) * cos (5 * π / 180) := by
    rw [show 10 * π / 180 = 15 * π / 180 - 5 * π / 180 by ring]
    rw [show 20 * π / 180 = 15 * π / 180 + 5 * π / 180 by ring]
    rw [cos_add, cos_sub]
    ring

  have htan : tan (15 * π / 180) = sin (15 * π / 180) / cos (15 * π / 180) := by
    rw [tan_eq_sin_div_cos]

  rw [htan]
  rw [h1, h2]

  have h3 : cos (5 * π / 180) ≠ 0 := by
    have h1 : 0 < 5 * π / 180 := by
      have hp : 0 < π := by linarith [Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    have h2 : cos (5 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [h1, Real.pi_pos]
      · linarith [h1, Real.pi_pos]
    linarith

  have h4 : cos (15 * π / 180) ≠ 0 := by
    have h1 : 0 < 15 * π / 180 := by
      have hp : 0 < π := by linarith [Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    have h2 : cos (15 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [h1, Real.pi_pos]
      · linarith [h1, Real.pi_pos]
    linarith
  field_simp [h3, h4]
  <;> ring_nf <;> field_simp [h3, h4] <;> ring