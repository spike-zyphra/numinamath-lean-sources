import Mathlib

open Real

theorem algebra_163960 : (cos (64 * π / 180) * cos (4 * π / 180) -
    cos (86 * π / 180) * cos (26 * π / 180)) /
    (cos (71 * π / 180) * cos (41 * π / 180) -
    cos (49 * π / 180) * cos (19 * π / 180)) = -1 := by
  have h1 : cos (64 * π / 180) * cos (4 * π / 180) - cos (86 * π / 180) * cos (26 * π / 180) = cos (68 * π / 180) := by
    have h1 : cos (64 * π / 180) * cos (4 * π / 180) = (cos (68 * π / 180) + cos (60 * π / 180)) / 2 := by
      rw [cos_add_cos]
      ring_nf
    have h2 : cos (86 * π / 180) * cos (26 * π / 180) = (cos (112 * π / 180) + cos (60 * π / 180)) / 2 := by
      rw [cos_add_cos]
      ring_nf
    have h3 : cos (112 * π / 180) = -cos (68 * π / 180) := by
      have h3 : 112 * π / 180 = π - 68 * π / 180 := by ring
      rw [h3]
      rw [cos_pi_sub]
    rw [h1, h2, h3]
    ring
  have h2 : cos (71 * π / 180) * cos (41 * π / 180) - cos (49 * π / 180) * cos (19 * π / 180) = -cos (68 * π / 180) := by
    have h1 : cos (71 * π / 180) * cos (41 * π / 180) = (cos (112 * π / 180) + cos (30 * π / 180)) / 2 := by
      rw [cos_add_cos]
      ring_nf
    have h2 : cos (49 * π / 180) * cos (19 * π / 180) = (cos (68 * π / 180) + cos (30 * π / 180)) / 2 := by
      rw [cos_add_cos]
      ring_nf
    have h3 : cos (112 * π / 180) = -cos (68 * π / 180) := by
      have h3 : 112 * π / 180 = π - 68 * π / 180 := by ring_nf
      rw [h3]
      rw [cos_pi_sub]
    rw [h1, h2, h3]
    ring_nf
  have h3 : cos (68 * π / 180) ≠ 0 := by
    apply ne_of_gt
    apply cos_pos_of_mem_Ioo
    constructor
    · -- 0 < 68°
      linarith [pi_pos]
    · -- 68° < 90°
      linarith [pi_pos]
  rw [h1, h2]
  field_simp [h3]