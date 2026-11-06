import Mathlib

open Real Set
open scoped Real

theorem inequalities_251387 (A B C : Real) (hA : A ∈ Ioo 0 π)
  (hB : B ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π) (hABC : A + B + C = π) :
  sin A + sin B + sin C ≤ 3 / 2 * sqrt 3 := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  have h1 : C = π - (A + B) := by 
    linarith 
  have h2 : sin C = sin (A + B) := by 
    rw [h1]
    have h3 : sin (π - (A + B)) = sin (A + B) := by 
      rw [sin_pi_sub]
    linarith [h3]
  have h5 : sin A + sin B + sin C = sin A + sin B + sin (A + B) := by 
    rw [show sin C = sin (A + B) by linarith [h2]]
  have h7 : sin A + sin B + sin (A + B) ≤ 3 / 2 * sqrt 3 := by 
    have h84 : sin (A + B) = sin A * cos B + cos A * sin B := by 
      rw [sin_add]
    -- have h5' : sin A + sin B + sin (A + B) = sin A + sin B + (sin A * cos B + cos A * sin B) := by 
    --   rw [h84]
    -- rewrite `LHS` using XY angle formula (have shown to be the right side max value of 3 / 2 * sqrt 3)
    have eq1 : sin A + sin B + sin (A + B) = 2 * sin ((A + B) / 2) * (cos ((A - B) / 2) + cos ((A + B) / 2)) := by 
      have eq2 : sin A + sin B = 2 * sin ((A + B) / 2) * cos ((A - B) / 2) := by 
        rw [show (A : ℝ) = (A + B) / 2 + (A - B) / 2 by ring]
        rw [show (B : ℝ) = (A + B) / 2 - (A - B) / 2 by ring]
        rw [sin_add, sin_sub]
        ring
      have eq3 : sin (A + B) = 2 * sin ((A + B) / 2) * cos ((A + B) / 2) := by 
        rw [show sin (A + B) = sin (2 * ((A + B) / 2)) by ring]
        rw [sin_two_mul]
        <;> ring_nf
      linarith [eq2, eq3]
    have eq1' : 2 * sin ((A + B) / 2) * (cos ((A - B) / 2) + cos ((A + B) / 2)) ≤ 3 / 2 * sqrt 3 := by 
      have h_A_B1 : 0 < (A + B) / 2 := by 
        nlinarith 
      have h_A_B2 : (A + B) / 2 < π / 2 := by 
        nlinarith 
      have h11 : sin ((A + B) / 2) > 0 := by 
        apply sin_pos_of_pos_of_lt_pi 
        linarith 
        linarith [show (A + B) / 2 < π by linarith] 
      have h12 : sin ((A + B) / 2) ^ 2 + cos ((A + B) / 2) ^ 2 = 1 := sin_sq_add_cos_sq ((A + B) / 2)
      have h13 : cos ((A - B) / 2) ≤ 1 := cos_le_one ((A - B) / 2)
      have h56 : cos ((A - B) / 2) ≥ -1 := by 
        have h57 : cos ((A - B) / 2) ≥ -1 := by 
          nlinarith [cos_sq_add_sin_sq ((A - B) / 2)]
        linarith 
      nlinarith [sq_nonneg (sin ((A + B) / 2) - sqrt 3 / 2), sq_nonneg (cos ((A + B) / 2) - 1 / 2), 
        sq_nonneg ((A + B) / 2 - π / 3), 
        sq_nonneg (cos ((A - B) / 2) - 1), 
        Real.sqrt_nonneg (3 : ℝ), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), 
        Real.sin_sq_add_cos_sq ((A + B) / 2), 
        sq_nonneg ((A - B) / 2), 
        mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)
      ]
    linarith [eq1, eq1']
  rw [h5] 
  linarith [h7]