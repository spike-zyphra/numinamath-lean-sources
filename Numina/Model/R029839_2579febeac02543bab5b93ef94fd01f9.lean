import Mathlib
open Real

theorem algebra_611085 : ((tan (π / 9))^2 - (sin (π / 9))^2)/ ((tan (π / 9))^2 * (sin (π / 9))^2)  = 1 := by
    have htan : tan (π / 9) = sin (π / 9) / cos (π / 9) := by
      rw [tan_eq_sin_div_cos]

    have h1 : sin (π / 9) ≠ 0 := by
      have h1 : 0 < π / 9 := by
        linarith [Real.pi_pos]
      have h2 : 0 < sin (π / 9) := by
        apply sin_pos_of_pos_of_lt_pi
        linarith [Real.pi_pos]
        linarith [Real.pi_pos]
      linarith

    have h2 : cos (π / 9) ≠ 0 := by
      have h3 : 0 < π / 9 := by
        linarith [Real.pi_pos]
      have h4 : cos (π / 9) > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      linarith

    rw [htan]

    have eq1 : ((sin (π / 9) / cos (π / 9)) ^ 2 - (sin (π / 9)) ^ 2) = (sin (π / 9)) ^ 4 / (cos (π / 9)) ^ 2 := by
      field_simp [h2]
      <;> nlinarith [Real.sin_sq_add_cos_sq (π / 9), sq_nonneg (sin (π / 9) ^ 2), sq_nonneg (cos (π / 9) ^ 2), sq_nonneg (sin (π / 9) - cos (π / 9)), sq_nonneg (sin (π / 9) + cos (π / 9))]

    have eq2 : ((sin (π / 9) / cos (π / 9)) ^ 2 * (sin (π / 9)) ^ 2) = (sin (π / 9)) ^ 4 / (cos (π / 9)) ^ 2 := by
      field_simp [h2]
      <;> ring

    rw [eq1, eq2]

    have h3 : (sin (π / 9)) ^ 4 / (cos (π / 9)) ^ 2 ≠ 0 := by
      have h4 : (sin (π / 9)) ^ 4 > 0 := by
        have h11 : sin (π / 9) > 0 := by
          apply sin_pos_of_pos_of_lt_pi
          linarith [Real.pi_pos]
          linarith [Real.pi_pos]
        positivity

      have h5 : (cos (π / 9)) ^ 2 > 0 := by
        have h6 : cos (π / 9) > 0 := by
          apply cos_pos_of_mem_Ioo
          constructor
          · linarith [Real.pi_pos]
          · linarith [Real.pi_pos]
        positivity
      have h7 : ( (sin (π / 9)) ^ 4 / (cos (π / 9)) ^ 2 ) > 0 := by
        apply div_pos
        linarith
        linarith
      linarith

    field_simp [h3]
    <;> ring