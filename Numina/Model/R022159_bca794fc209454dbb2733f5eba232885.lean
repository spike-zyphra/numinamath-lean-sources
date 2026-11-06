import Mathlib

open Real

theorem calculus_13085 : (1 + tan (π / 9)) * (1 + tan (5 * π / 36)) = 2 := by
  have h1 : π / 9 + 5 * π / 36 = π / 4 := by 
    linarith [Real.pi_pos]

  have h2 : tan (π / 9 + 5 * π / 36) = 1 := by 
    rw [h1]
    exact tan_pi_div_four

  have htan1 : tan (π / 9 + 5 * π / 36) = (tan (π / 9) + tan (5 * π / 36)) / (1 - tan (π / 9) * tan (5 * π / 36)) := by
    have htan_eq : tan (π / 9 + 5 * π / 36) = sin (π / 9 + 5 * π / 36) / cos (π / 9 + 5 * π / 36) := by
      rw [tan_eq_sin_div_cos]
    rw [htan_eq]
    have hsin : sin (π / 9 + 5 * π / 36) = sin (π / 9) * cos (5 * π / 36) + cos (π / 9) * sin (5 * π / 36) := by
      rw [sin_add]
    have hcos : cos (π / 9 + 5 * π / 36) = cos (π / 9) * cos (5 * π / 36) - sin (π / 9) * sin (5 * π / 36) := by
      rw [cos_add]
    rw [hsin, hcos]
    have htan1' : tan (π / 9) = sin (π / 9) / cos (π / 9) := by
      rw [tan_eq_sin_div_cos]
    have htan2' : tan (5 * π / 36) = sin (5 * π / 36) / cos (5 * π / 36) := by
      rw [tan_eq_sin_div_cos]
    rw [htan1', htan2']
    have hcos1 : cos (π / 9) ≠ 0 := by 
      have h1 : 0 < π / 9 := by linarith [Real.pi_pos]
      have h2 : π / 9 < π / 2 := by linarith [Real.pi_pos]
      have hcos_pos : 0 < cos (π / 9) := by
        apply cos_pos_of_mem_Ioo
        constructor
        linarith
        linarith
      linarith
    have hcos2 : cos (5 * π / 36) ≠ 0 := by 
      have h1 : 0 < 5 * π / 36 := by linarith [Real.pi_pos]
      have h2 : 5 * π / 36 < π / 2 := by linarith [Real.pi_pos]
      have hcos_pos : 0 < cos (5 * π / 36) := by
        apply cos_pos_of_mem_Ioo
        constructor
        linarith
        linarith
      linarith
    field_simp [hcos1, hcos2]
    <;> ring_nf
    <;> field_simp [hcos1, hcos2]
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num
    <;> norm_num [Real.sin_sq, Real.cos_sq] <;> nlinarith
  have h3 : 1 - tan (π / 9) * tan (5 * π / 36) ≠ 0 := by 
    by_contra h
    have eq1 : tan (π / 9 + 5 * π / 36) = (tan (π / 9) + tan (5 * π / 36)) / (1 - tan (π / 9) * tan (5 * π / 36)) := htan1
    rw [h] at eq1 
    have eq2 : (tan (π / 9) + tan (5 * π / 36)) / (1 - tan (π / 9) * tan (5 * π / 36)) = 0 := by 
      rw [h]
      norm_num 
    have htan3 : tan (π / 9 + 5 * π / 36) = 0 := by linarith [eq1, eq2]
    linarith [h2, htan3]
  have h4 : tan (π / 9) + tan (5 * π / 36) = 1 - tan (π / 9) * tan (5 * π / 36) := by
    rw [htan1] at h2 
    field_simp [h3] at h2 ⊢ 
    linarith [h2] 
    all_goals try { tauto <;> try { nlinarith [Real.pi_pos] } } <;> try { nlinarith [Real.pi_pos] }
  calc
    (1 + tan (π / 9)) * (1 + tan (5 * π / 36)) = 1 + (tan (π / 9) + tan (5 * π / 36)) + tan (π / 9) * tan (5 * π / 36) := by
      ring
    _ = 1 + (1 - tan (π / 9) * tan (5 * π / 36)) + tan (π / 9) * tan (5 * π / 36) := by 
      rw [h4] 
    _ = 2 := by 
      ring