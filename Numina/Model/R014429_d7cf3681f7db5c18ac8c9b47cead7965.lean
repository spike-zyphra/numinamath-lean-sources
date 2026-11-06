import Mathlib

open Real Set
open scoped Real

theorem algebra_196094 (α : ℝ) :
  cos ((5 / 2) * π - 6 * α) * sin (π - 2 * α) ^ 3 -
  cos (6 * α - π) * sin (π / 2 - 2 * α) ^ 3 =
  cos (4 * α) ^ 3 := by 
  have h1 : cos ((5 / 2) * π - 6 * α) = sin (6 * α) := by 
    have h2 : cos ((5 / 2) * π - 6 * α) = cos (Real.pi / 2 - 6 * α + 2 * Real.pi) := by 
      ring_nf
    rw [h2]
    have h3 : cos (Real.pi / 2 - 6 * α + 2 * Real.pi) = cos (Real.pi / 2 - 6 * α) := by 
      rw [cos_add_two_pi]
    rw [h3]
    have h4 : cos (Real.pi / 2 - 6 * α) = sin (6 * α) := by 
      rw [cos_pi_div_two_sub]
    exact h4
  have h2 : sin (π - 2 * α) = sin (2 * α) := by 
    rw [sin_pi_sub]
  have h3 : cos (6 * α - π) = -cos (6 * α) := by
    have h4 : cos (6 * α - π) = cos (6 * α - Real.pi) := by
      ring_nf 
    rw [h4]
    have h6 : cos (6 * α - Real.pi) = -cos (6 * α) := by 
      have h9 : cos (6 * α - Real.pi) = -cos (6 * α) := by 
        rw [show 6 * α - Real.pi = (6 * α) - Real.pi by ring]
        rw [cos_sub]
        simp [cos_pi, sin_pi]
      linarith 
    exact h6
  have h4 : sin (π / 2 - 2 * α) = cos (2 * α) := by 
    rw [sin_pi_div_two_sub]
  rw [h1, h2, h3, h4]
  have h5 : sin (6 * α) = 3 * sin (2 * α) - 4 * sin (2 * α) ^ 3 := by
    have h8 : sin (6 * α) = sin (3 * (2 * α)) := by ring_nf 
    rw [h8]
    rw [show sin (3 * (2 * α)) = 3 * sin (2 * α) - 4 * sin (2 * α) ^ 3 by 
      rw [sin_three_mul]
    ]
  have h6 : cos (6 * α) = 4 * cos (2 * α) ^ 3 - 3 * cos (2 * α) := by
    have h7 : cos (6 * α) = cos (3 * (2 * α)) := by ring_nf
    rw [h7]
    rw [show cos (3 * (2 * α)) = 4 * cos (2 * α) ^ 3 - 3 * cos (2 * α) by 
      rw [cos_three_mul]
    ]
  have h7 : cos (4 * α) = 2 * cos (2 * α) ^ 2 - 1 := by
    have h8 : cos (4 * α) = cos (2 * (2 * α) ) := by 
      ring_nf 
    rw [h8]
    rw [cos_two_mul]
  rw [h5, h6, h7]
  have h8 : sin (2 * α) ^ 2 = 1 - cos (2 * α) ^ 2 := by 
    have h2_sq : sin (2 * α) ^ 2 + cos (2 * α) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq (2 * α)
    linarith 
  have eq3 : (3 * sin (2 * α) - 4 * sin (2 * α) ^ 3) * sin (2 * α) ^ 3 + (4 * cos (2 * α) ^ 3 - 3 * cos (2 * α)) * cos (2 * α) ^ 3 = (2 * cos (2 * α) ^ 2 - 1) ^ 3 := by 
    have eq1' : sin (2 * α) ^ 2 = 1 - cos (2 * α) ^ 2 := h8
    have eq2' : sin (2 * α) ^ 3 = sin (2 * α) * (1 - cos (2 * α) ^ 2) := by 
      calc 
        sin (2 * α) ^ 3 = sin (2 * α) * sin (2 * α) ^ 2 := by ring 
        _ = sin (2 * α) * (1 - cos (2 * α) ^ 2) := by rw [eq1']
    have eq3' : sin (2 * α) ^ 4 = (1 - cos (2 * α) ^ 2) ^ 2 := by
      calc
        sin (2 * α) ^ 4 = (sin (2 * α) ^ 2) ^ 2 := by ring
        _ = (1 - cos (2 * α) ^ 2) ^ 2 := by rw [eq1']
    have eq4' : sin (2 * α) ^ 6 = (1 - cos (2 * α) ^ 2) ^ 3 := by 
      calc
        sin (2 * α) ^ 6 = (sin (2 * α) ^ 2) ^ 3 := by ring 
        _ = (1 - cos (2 * α) ^ 2) ^ 3 := by rw [eq1']
    nlinarith [sq_nonneg (sin (2 * α) ), sq_nonneg (cos (2 * α) - 1 ), sq_nonneg (cos (2 * α) + 1 ), sq_nonneg (sin (2 * α) * cos (2 * α) ), sq_nonneg (sin (2 * α) ^ 2 - (1 - cos (2 * α) ^ 2) ), Real.sin_sq_add_cos_sq (2 * α), sq_nonneg (cos (2 * α) ^ 2 - 1 / 2 ), sq_nonneg (sin (2 * α) * (1 - cos (2 * α) ^ 2) ) ]
  linarith [eq3]