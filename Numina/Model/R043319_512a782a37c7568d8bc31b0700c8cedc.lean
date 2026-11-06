import Mathlib

open Real

theorem algebra_178669 (α : ℝ) (hα : cos (α / 2) ≠ 0) :
    cos ((5 * π / 2 - α)) * sin ((π / 2) + (α / 2)) /
    ((2 * sin ((π - α) / 2) + cos ((3 * π / 2 - α))) * cos ((π - α) / 4) ^ 2) =
    2 * tan (α / 2) := by
  have h1 : cos (5 * π / 2 - α) = sin α := by 
    have h2 : 5 * π / 2 - α = π / 2 - α + 2 * π := by 
      ring_nf
    rw [h2]
    have h3 : cos (π / 2 - α + 2 * π) = cos (π / 2 - α) := by 
      have h4 : cos (π / 2 - α + 2 * π) = cos ((π / 2 - α) + 2 * π) := by ring_nf
      rw [h4]
      rw [cos_add_two_pi]
    rw [h3]
    have h4 : cos (π / 2 - α) = sin α := by 
      rw [cos_pi_div_two_sub]
    exact h4

  have h2 : sin (π / 2 + α / 2) = cos (α / 2) := by 
    rw [sin_add]
    rw [sin_pi_div_two, cos_pi_div_two]
    ring_nf

  have h3 : 2 * sin ((π - α) / 2) = 2 * cos (α / 2) := by
    have h4 : sin ((π - α) / 2) = cos (α / 2) := by
      have h5 : (π - α) / 2 = π / 2 - α / 2 := by ring_nf
      rw [h5]
      rw [sin_pi_div_two_sub]
      all_goals ring_nf
      all_goals simp [sin_sq, cos_sq] 
    rw [h4]
    all_goals ring_nf

  have h4 : cos (3 * π / 2 - α) = -sin α := by
    have h5 : 3 * π / 2 - α = π + (π / 2 - α) := by 
      ring_nf
    rw [h5]
    have h6 : cos (π + (π / 2 - α)) = -cos (π / 2 - α) := by 
      rw [cos_add]
      simp [cos_pi, sin_pi]
      <;> ring_nf <;> simp [sin_sq, cos_sq]
      <;> ring_nf
    rw [h6]
    have h7 : cos (π / 2 - α) = sin α := by 
      rw [cos_pi_div_two_sub]
    rw [h7]
    <;> ring_nf
  
  have h5 : cos ((π - α) / 4) ^ 2 = (1 + sin (α / 2)) / 2 := by
    have h6 : cos ((π - α) / 4) ^ 2 = (1 + cos ((π - α) / 2)) / 2 := by 
      have h7 : cos ((π - α) / 4) ^ 2 = (1 + cos (2 * ((π - α) / 4)) ) / 2 := by
        rw [cos_sq]
        <;> ring_nf 
        all_goals simp [sin_sq, cos_sq]
      have h8 : 2 * ((π - α) / 4) = (π - α) / 2 := by
        ring_nf
      rw [h8] at h7
      linarith [h7]
    rw [h6]
    have h7 : cos ((π - α) / 2) = sin (α / 2) := by
      have h8 : (π - α) / 2 = π / 2 - α / 2 := by
        ring_nf
      rw [h8]
      rw [cos_pi_div_two_sub]
      all_goals ring_nf
      all_goals simp [sin_sq, cos_sq]
    rw [h7]
    all_goals ring_nf

  have h6 : sin α = 2 * sin (α / 2) * cos (α / 2) := by 
    rw [←sin_two_mul]
    ring_nf

  have htan : tan (α / 2) = sin (α / 2) / cos (α / 2) := by 
    rw [tan_eq_sin_div_cos]

  have eq7 : cos ((5 * π / 2 - α)) * sin ((π / 2) + (α / 2)) = 2 * sin (α / 2) * cos (α / 2) ^ 2 := by 
    rw [h1, h2, h6]
    <;> ring_nf 
    <;> simp [sin_sq]
    <;> ring_nf 
  have eq8 : (2 * sin ((π - α) / 2) + cos ((3 * π / 2 - α))) * cos ((π - α) / 4) ^ 2 = cos (α / 2) ^ 3 := by
    have eq81 : 2 * sin ((π - α) / 2) = 2 * cos (α / 2) := h3
    have eq82 : cos ((3 * π / 2 - α)) = - sin α := h4
    have eq83 : 2 * sin ((π - α) / 2) + cos ((3 * π / 2 - α)) = 2 * cos (α / 2) - sin α := by 
      linarith [eq81, eq82]
    have eq84 : 2 * cos (α / 2) - sin α = 2 * cos (α / 2) * (1 - sin (α / 2)) := by 
      rw [h6]
      <;> ring_nf 
      <;> simp [sin_sq, cos_sq]
      <;> ring_nf 
    have eq85 : cos ((π - α) / 4) ^ 2 = (1 + sin (α / 2) ) / 2 := h5
    calc
      (2 * sin ((π - α) / 2) + cos ((3 * π / 2 - α))) * cos ((π - α) / 4) ^ 2
        = (2 * cos (α / 2) - sin α) * cos ((π - α) / 4) ^ 2 := by 
          rw [eq83]
      _ = (2 * cos (α / 2) * (1 - sin (α / 2)) ) * cos ((π - α) / 4) ^ 2 := by 
        rw [eq84]
      _ = (2 * cos (α / 2) * (1 - sin (α / 2)) ) * ((1 + sin (α / 2) ) / 2) := by 
        rw [eq85]
      _ = cos (α / 2) * (1 - sin (α / 2) ) * (1 + sin (α / 2) ) := by 
        ring_nf 
      _ = cos (α / 2) * (1 - sin (α / 2) ^ 2 ) := by 
        ring_nf 
      _ = cos (α / 2) * cos (α / 2)^2 := by 
        have h88 : 1 - sin (α / 2) ^ 2 = cos (α / 2) ^ 2 := by 
          have h89 : sin (α / 2) ^ 2 + cos (α / 2) ^ 2 = 1 := by 
            exact Real.sin_sq_add_cos_sq (α / 2)
          linarith
        rw [h88]
        <;> ring_nf 
      _ = cos (α / 2) ^ 3 := by 
        ring_nf

  have eq9 : cos ((5 * π / 2 - α)) * sin ((π / 2) + (α / 2)) / ((2 * sin ((π - α) / 2) + cos ((3 * π / 2 - α))) * cos ((π - α) / 4) ^ 2) = (2 * sin (α / 2) * cos (α / 2) ^ 2 ) / cos (α / 2) ^ 3 := by 
    rw [eq7, eq8]

  rw [eq9]
  have eq10 : (2 * sin (α / 2) * cos (α / 2) ^ 2 ) / cos (α / 2) ^ 3 = (2 * sin (α / 2) / cos (α / 2) ) := by 
    field_simp [show cos (α / 2) ≠ 0 by exact hα]
    <;> ring_nf 
    <;> field_simp [show cos (α / 2) ≠ 0 by exact hα]
    all_goals nlinarith 
  rw [eq10]
  rw [htan]
  <;> field_simp [show cos (α / 2) ≠ 0 by exact hα] 
  <;> ring_nf 
  <;> field_simp [hα]
  all_goals field_simp [show cos (α / 2) ≠ 0 by exact hα]
  <;> linarith