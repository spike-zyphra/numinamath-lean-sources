import Mathlib

open Real Set


theorem algebra_291072 (x : ℝ) (hx : 1 + Real.sin x ≠ 0):
    Real.tan (Real.pi / 4 - x / 2) = Real.cos x / (1 + Real.sin x) := by

  have h1 : Real.cos (Real.pi / 4 - x / 2) ≠ 0 := by
    by_contra h
    have h2 : 1 + Real.sin x = 0 := by
      have h0 : 1 + Real.sin x = 2 * Real.cos (Real.pi / 4 - x / 2) ^ 2 := by
        have h5 : Real.cos (Real.pi / 4 - x / 2) ^ 2 = (1 + Real.sin x) / 2 := by
          have h7 : Real.cos (Real.pi / 4 - x / 2) ^ 2 = (1 + Real.cos (2 * (Real.pi / 4 - x / 2)) ) / 2 := by
            rw [cos_sq]
            <;> ring_nf
          have h50 : Real.cos (2 * (Real.pi / 4 - x / 2)) = Real.sin x := by
            have h10 : 2 * (Real.pi / 4 - x / 2) = Real.pi / 2 - x := by
              ring_nf
            rw [h10]
            rw [show Real.cos (Real.pi / 2 - x) = Real.sin x by
              rw [Real.cos_pi_div_two_sub x]
            ]
          rw [h50] at h7
          linarith
        linarith
      have h11 : Real.cos (Real.pi / 4 - x / 2) ^ 2 = 0 := by
        rw [h]
        norm_num
      rw [h11] at h0
      nlinarith
    contradiction

  have htan : Real.tan (Real.pi / 4 - x / 2) = Real.sin (Real.pi / 4 - x / 2) / Real.cos (Real.pi / 4 - x / 2) := by
    rw [Real.tan_eq_sin_div_cos]

  rw [htan]

  have h3 : Real.sin (Real.pi / 4 - x / 2) = (Real.sqrt 2 / 2) * (Real.cos (x / 2) - Real.sin (x / 2)) := by
    have h7 : Real.sin (Real.pi / 4 - x / 2) = Real.sin (Real.pi / 4) * Real.cos (x / 2) - Real.cos (Real.pi / 4) * Real.sin (x / 2) := by
      rw [Real.sin_sub]
    have h8 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [Real.sin_pi_div_four]
    have h9 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [Real.cos_pi_div_four]
    rw [h7, h8, h9]
    all_goals ring_nf

  have h4 : Real.cos (Real.pi / 4 - x / 2) = (Real.sqrt 2 / 2) * (Real.cos (x / 2) + Real.sin (x / 2)) := by
    have h5 : Real.cos (Real.pi / 4 - x / 2) = Real.cos (Real.pi / 4) * Real.cos (x / 2) + Real.sin (Real.pi / 4) * Real.sin (x / 2) := by
      rw [Real.cos_sub]
    have h8 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [Real.sin_pi_div_four]
    have h9 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [Real.cos_pi_div_four]
    rw [h5, h8, h9]
    all_goals ring_nf

  rw [h3, h4]

  have h5 : Real.cos x = (Real.cos (x / 2) ^ 2 - Real.sin (x / 2) ^ 2 : ℝ) := by
    have h8 : Real.cos x = Real.cos (2 * (x / 2)) := by
      ring_nf
    rw [h8]
    have h9 : Real.cos (2 * (x / 2)) = 2 * Real.cos (x / 2) ^ 2 - 1 := by
      rw [Real.cos_two_mul]
    have h10 : Real.sin (x / 2) ^ 2 + Real.cos (x / 2) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq (x / 2)
    nlinarith

  have h6 : (1 + Real.sin x) = (Real.cos (x / 2) + Real.sin (x / 2)) ^ 2 := by
    have h7 : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
      have h8 : Real.sin x = Real.sin (2 * (x / 2)) := by
        ring_nf
      rw [h8]
      have h9 : Real.sin (2 * (x / 2)) = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
        rw [Real.sin_two_mul]
      linarith
    nlinarith [sq_nonneg (Real.cos (x / 2) - Real.sin (x / 2)), sq_nonneg (Real.cos (x / 2) + Real.sin (x / 2)), Real.sin_sq_add_cos_sq (x / 2)]

  have h77 : (Real.cos (x / 2) + Real.sin (x / 2)) ≠ 0 := by
    by_contra h
    have h9 : Real.cos (Real.pi / 4 - x / 2) = 0 := by
      have h99 : Real.cos (Real.pi / 4 - x / 2) = (Real.sqrt 2 / 2) * (Real.cos (x / 2) + Real.sin (x / 2)) := h4
      rw [h99]
      have h10 : Real.cos (x / 2) + Real.sin (x / 2) = 0 := by
        nlinarith [h]
      rw [h10]
      norm_num
    contradiction

  have eq2 : (Real.sqrt 2 / 2) * (Real.cos (x / 2) - Real.sin (x / 2)) / ((Real.sqrt 2 / 2) * (Real.cos (x / 2) + Real.sin (x / 2))) = (Real.cos x) / (1 + Real.sin x) := by
    have h777 : Real.cos (x / 2) + Real.sin (x / 2) ≠ 0 := h77
    have : (Real.sqrt 2 / 2) * (Real.cos (x / 2) - Real.sin (x / 2)) / ((Real.sqrt 2 / 2) * (Real.cos (x / 2) + Real.sin (x / 2))) = (Real.cos (x / 2) - Real.sin (x / 2)) / (Real.cos (x / 2) + Real.sin (x / 2)) := by
      have h111 : Real.sqrt 2 / 2 ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      have h777 : Real.cos (x / 2) + Real.sin (x / 2) ≠ 0 := h77
      field_simp [h777, h111]
      <;> nlinarith
    rw [this]
    have h8 : (Real.cos (x / 2) - Real.sin (x / 2)) / (Real.cos (x / 2) + Real.sin (x / 2)) = (Real.cos x) / (1 + Real.sin x) := by
      have eq2 : Real.cos x = (Real.cos (x / 2) ^ 2 - Real.sin (x / 2) ^ 2 : ℝ) := h5
      have eq3 : (1 + Real.sin x) = (Real.cos (x / 2) + Real.sin (x / 2)) ^ 2 := h6
      have h777 : Real.cos (x / 2) + Real.sin (x / 2) ≠ 0 := h77
      rw [eq2, eq3]
      have eq5 : (Real.cos (x / 2) ^ 2 - Real.sin (x / 2) ^ 2) = (Real.cos (x / 2) + Real.sin (x / 2)) * (Real.cos (x / 2) - Real.sin (x / 2)) := by
        nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
      rw [eq5]
      field_simp [h777, show (Real.cos (x / 2) + Real.sin (x / 2)) ≠ 0 by exact h777]
      <;> nlinarith
    linarith

  nlinarith [eq2, Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]