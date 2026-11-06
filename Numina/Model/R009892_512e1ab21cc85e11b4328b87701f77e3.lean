import Mathlib

open Real

theorem algebra_225606 :
    Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) * Real.cos (8 * Real.pi / 7) = 1 / 8 ∧
    Real.cos (2 * Real.pi / 9) * Real.cos (4 * Real.pi / 9) * Real.cos (8 * Real.pi / 9) = -1 / 8 := by
  constructor
  · -- First part: proving $\cos \frac{2 \pi}{7} \cos \frac{4 \pi}{7} \cos \frac{8 \pi}{7} = \frac{1}{8}$
    have h2 : Real.sin (2 * Real.pi / 7) ≠ 0 := by
      have h3 : 0 < 2 * Real.pi / 7 := by 
        nlinarith [Real.pi_pos]
      have h4 : Real.sin (2 * Real.pi / 7) > 0 := by
        apply Real.sin_pos_of_pos_of_lt_pi
        all_goals nlinarith [Real.pi_pos]
      nlinarith
    have h3 : Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) * Real.cos (8 * Real.pi / 7) =
          (Real.sin (16 * Real.pi / 7)) / (8 * Real.sin (2 * Real.pi / 7)) := by
      have h4 : Real.sin (4 * Real.pi / 7) = 2 * Real.sin (2 * Real.pi / 7) * Real.cos (2 * Real.pi / 7) := by 
        rw [← Real.sin_two_mul (2 * Real.pi / 7)]
        ring_nf
      have h5 : Real.sin (8 * Real.pi / 7) = 2 * Real.sin (4 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) := by
        rw [← Real.sin_two_mul (4 * Real.pi / 7)]
        ring_nf
      have h6 : Real.sin (16 * Real.pi / 7) = 2 * Real.sin (8 * Real.pi / 7) * Real.cos (8 * Real.pi / 7) := by 
        rw [← Real.sin_two_mul (8 * Real.pi / 7)]
        ring_nf
      calc 
        Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) * Real.cos (8 * Real.pi / 7)
          = (Real.sin (4 * Real.pi / 7) / (2 * Real.sin (2 * Real.pi / 7))) * Real.cos (4 * Real.pi / 7) * Real.cos (8 * Real.pi / 7) := by 
            rw [h4]
            field_simp [h2]
            <;> ring_nf <;> simp [Real.sin_eq_zero] <;> linarith [Real.pi_pos]
        _ = (Real.sin (8 * Real.pi / 7) / (4 * Real.sin (2 * Real.pi / 7))) * Real.cos (8 * Real.pi / 7) := by
          rw [h5]
          field_simp [h2]
          <;> ring_nf <;> simp [Real.sin_eq_zero] <;> linarith [Real.pi_pos]
        _ = (Real.sin (16 * Real.pi / 7) / (8 * Real.sin (2 * Real.pi / 7))) := by 
          rw [h6]
          field_simp [h2]
          <;> ring_nf <;> simp [Real.sin_eq_zero] <;> linarith [Real.pi_pos]
    have h4 : Real.sin (16 * Real.pi / 7) = Real.sin (2 * Real.pi / 7) := by 
      have h5 : 16 * Real.pi / 7 = 2 * Real.pi + 2 * Real.pi / 7 := by 
        linarith [Real.pi_pos]
      rw [h5]
      have h6 : Real.sin (2 * Real.pi + 2 * Real.pi / 7) = Real.sin (2 * Real.pi / 7) := by
        rw [Real.sin_add, Real.sin_two_pi, Real.cos_two_pi]
        ring_nf
      linarith [h6]
    rw [h4] at h3 
    have h7 : Real.sin (2 * Real.pi / 7) / (8 * Real.sin (2 * Real.pi / 7)) = 1 / 8 := by
      field_simp [h2]
      <;> ring
    field_simp [h3] at *
    <;> nlinarith [Real.pi_pos]
  · -- Second part: proving $\cos \frac{2 \pi}{9} \cos \frac{4 \pi}{9} \cos \frac{8 \pi}{9} = -\frac{1}{8}$
    have h2 : Real.sin (2 * Real.pi / 9) ≠ 0 := by
      have h3 : 0 < 2 * Real.pi / 9 := by 
        nlinarith [Real.pi_pos]
      have h4 : Real.sin (2 * Real.pi / 9) > 0 := by
        apply Real.sin_pos_of_pos_of_lt_pi
        all_goals nlinarith [Real.pi_pos]
      nlinarith
    have h3 : Real.cos (2 * Real.pi / 9) * Real.cos (4 * Real.pi / 9) * Real.cos (8 * Real.pi / 9) =
          (Real.sin (16 * Real.pi / 9)) / (8 * Real.sin (2 * Real.pi / 9)) := by
      have h4 : Real.sin (4 * Real.pi / 9) = 2 * Real.sin (2 * Real.pi / 9) * Real.cos (2 * Real.pi / 9) := by 
        rw [← Real.sin_two_mul (2 * Real.pi / 9)]
        ring_nf
      have h5 : Real.sin (8 * Real.pi / 9) = 2 * Real.sin (4 * Real.pi / 9) * Real.cos (4 * Real.pi / 9) := by
        rw [← Real.sin_two_mul (4 * Real.pi / 9)]
        ring_nf
      have h6 : Real.sin (16 * Real.pi / 9) = 2 * Real.sin (8 * Real.pi / 9) * Real.cos (8 * Real.pi / 9) := by 
        rw [← Real.sin_two_mul (8 * Real.pi / 9)]
        ring_nf
      calc 
        Real.cos (2 * Real.pi / 9) * Real.cos (4 * Real.pi / 9) * Real.cos (8 * Real.pi / 9)
          = (Real.sin (4 * Real.pi / 9) / (2 * Real.sin (2 * Real.pi / 9))) * Real.cos (4 * Real.pi / 9) * Real.cos (8 * Real.pi / 9) := by 
            rw [h4]
            field_simp [h2]
            <;> ring_nf <;> simp [Real.sin_eq_zero] <;> linarith [Real.pi_pos]
        _ = (Real.sin (8 * Real.pi / 9) / (4 * Real.sin (2 * Real.pi / 9))) * Real.cos (8 * Real.pi / 9) := by
          rw [h5]
          field_simp [h2]
          <;> ring_nf <;> simp [Real.sin_eq_zero] <;> linarith [Real.pi_pos]
        _ = (Real.sin (16 * Real.pi / 9) / (8 * Real.sin (2 * Real.pi / 9))) := by 
          rw [h6]
          field_simp [h2]
          <;> ring_nf <;> simp [Real.sin_eq_zero] <;> linarith [Real.pi_pos]
    have h4 : Real.sin (16 * Real.pi / 9) = - Real.sin (2 * Real.pi / 9) := by 
      have h5 : 16 * Real.pi / 9 = 2 * Real.pi - 2 * Real.pi / 9 := by 
        linarith [Real.pi_pos]
      rw [h5]
      have h6 : Real.sin (2 * Real.pi - 2 * Real.pi / 9) = - Real.sin (2 * Real.pi / 9) := by
        rw [Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi]
        ring_nf
      linarith [h6]
    rw [h4] at h3 
    have h7_neg : (- Real.sin (2 * Real.pi / 9) ) / (8 * Real.sin (2 * Real.pi / 9)) = -1 / 8 := by
      have h8 : Real.sin (2 * Real.pi / 9) ≠ 0 := h2
      field_simp [h8]
      <;> ring
    field_simp [h3] at *
    <;> nlinarith [Real.pi_pos]