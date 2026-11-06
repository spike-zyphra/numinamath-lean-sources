import Mathlib

open Real

theorem algebra_244456 : cos (π/11) - cos (2*π/11) + cos (3*π/11) - cos (4*π/11) + cos (5*π/11) = 1/2 := by
  have h2 : sin (π / 11) ≠ 0 := by
    apply ne_of_gt
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have eq1 : (cos (π/11) - cos (2*π/11) + cos (3*π/11) - cos (4*π/11) + cos (5*π/11)) * (2 * sin (π / 11)) = sin (π / 11) := by
    have h7 : (cos (π/11) - cos (2*π/11) + cos (3*π/11) - cos (4*π/11) + cos (5*π/11)) * (2 * sin (π / 11)) =
        (2 * sin (π / 11) * cos (π / 11)) - (2 * sin (π / 11) * cos (2 * π / 11)) + (2 * sin (π / 11) * cos (3 * π / 11)) - (2 * sin (π / 11) * cos (4 * π / 11)) + (2 * sin (π / 11) * cos (5 * π / 11)) := by ring
    rw [h7]
    have h8 : 2 * sin (π / 11) * cos (π / 11) = sin (2 * (π / 11)) := by
      rw [show 2 * sin (π / 11) * cos (π / 11) = 2 * sin (π / 11) * cos (π / 11) by ring]
      rw [←sin_two_mul]
      all_goals ring
    have h9 : 2 * sin (π / 11) * cos (2 * π / 11) = sin (3 * (π / 11)) + sin ((- (π / 11))) := by
      rw [show 2 * sin (π / 11) * cos (2 * π / 11) = 2 * sin (π / 11) * cos (2 * π / 11) by ring]
      rw [show 2 * sin (π / 11) * cos (2 * π / 11) = sin ((π / 11) + (2 * π / 11)) + sin ((π / 11) - (2 * π / 11)) by rw [sin_add, sin_sub]; ring]
      <;> ring_nf
    have h10 : 2 * sin (π / 11) * cos (3 * π / 11) = sin (4 * (π / 11)) + sin ((-2 * (π / 11))) := by
      rw [show 2 * sin (π / 11) * cos (3 * π / 11) = 2 * sin (π / 11) * cos (3 * π / 11) by ring]
      rw [show 2 * sin (π / 11) * cos (3 * π / 11) = sin ((π / 11) + (3 * π / 11)) + sin ((π / 11) - (3 * π / 11)) by rw [sin_add, sin_sub]; ring]
      <;> ring_nf
    have h11 : 2 * sin (π / 11) * cos (4 * π / 11) = sin (5 * (π / 11)) + sin ((-3 * (π / 11))) := by
      rw [show 2 * sin (π / 11) * cos (4 * π / 11) = 2 * sin (π / 11) * cos (4 * π / 11) by ring]
      rw [show 2 * sin (π / 11) * cos (4 * π / 11) = sin ((π / 11) + (4 * π / 11)) + sin ((π / 11) - (4 * π / 11)) by rw [sin_add, sin_sub]; ring]
      <;> ring_nf
    have h12 : 2 * sin (π / 11) * cos (5 * π / 11) = sin (6 * (π / 11)) + sin ((-4 * (π / 11))) := by
      rw [show 2 * sin (π / 11) * cos (5 * π / 11) = 2 * sin (π / 11) * cos (5 * π / 11) by ring]
      rw [show 2 * sin (π / 11) * cos (5 * π / 11) = sin ((π / 11) + (5 * π / 11)) + sin ((π / 11) - (5 * π / 11)) by rw [sin_add, sin_sub]; ring]
      <;> ring_nf
    rw [h8, h9, h10, h11, h12]
    have h14 : sin ((- (π / 11))) = -sin (π / 11) := by 
      rw [sin_neg]
    have h16 : sin ((-2 * (π / 11))) = -sin (2 * (π / 11)) := by
      rw [show -2 * (π / 11) = - (2 * (π / 11)) by ring]
      rw [sin_neg]
    have h18 : sin ((-3 * (π / 11))) = -sin (3 * (π / 11)) := by
      rw [show -3 * (π / 11) = - (3 * (π / 11)) by ring]
      rw [sin_neg]
    have h20 : sin ((-4 * (π / 11))) = -sin (4 * (π / 11)) := by
      rw [show -4 * (π / 11) = - (4 * (π / 11)) by ring]
      rw [sin_neg]
    have h21 : sin (6 * (π / 11)) = sin (5 * (π / 11)) := by
      have h22 : 6 * (π / 11) = Real.pi - (5 * (π / 11)) := by 
        linarith [Real.pi_pos]
      rw [h22]
      rw [sin_pi_sub]
    simp only [h14, h16, h18, h20, h21]
    ring_nf
  have eq2 : (cos (π/11) - cos (2*π/11) + cos (3*π/11) - cos (4*π/11) + cos (5*π/11)) = (1 / 2 : ℝ) := by
    have h7 : (cos (π/11) - cos (2*π/11) + cos (3*π/11) - cos (4*π/11) + cos (5*π/11)) * (2 * sin (π / 11)) = sin (π / 11) := eq1
    have h8 : sin (π / 11) ≠ 0 := h2
    have eq3 : (cos (π/11) - cos (2*π/11) + cos (3*π/11) - cos (4*π/11) + cos (5*π/11)) = sin (π / 11) / (2 * sin (π / 11)) := by
      field_simp [h8] at h7 ⊢
      linarith
    rw [eq3]
    have h9 : sin (π / 11) / (2 * sin (π / 11)) = (1 / 2 : ℝ) := by
      have h10 : sin (π / 11) ≠ 0 := h8
      field_simp [h10]
      <;> nlinarith
    linarith [h9]
  exact_mod_cast eq2