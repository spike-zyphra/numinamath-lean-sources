import Mathlib

open Real Set
open scoped Real

theorem algebra_162548 (α β : ℝ) :
  sin (2 * α) ^ 2 + sin β ^ 2 + cos (2 * α + β) * cos (2 * α - β) = 1 := by
  have h1 : cos (2 * α + β) = cos (2 * α) * cos β - sin (2 * α) * sin β := by 
    rw [cos_add]
  have h2 : cos (2 * α - β) = cos (2 * α) * cos β + sin (2 * α) * sin β := by 
    rw [cos_sub]
  rw [h1, h2]
  have h3 : sin (2 * α) ^ 2 + cos (2 * α) ^ 2 = 1 := by 
    exact Real.sin_sq_add_cos_sq (2 * α)
  have h4 : sin β ^ 2 + cos β ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq β
  have eq5 : (cos (2 * α) * cos β - sin (2 * α) * sin β) * (cos (2 * α) * cos β + sin (2 * α) * sin β) =
      cos (2 * α) ^ 2 * cos β ^ 2 - sin (2 * α) ^ 2 * sin β ^ 2 := by 
    ring
  have eq6 : sin (2 * α) ^ 2 + sin β ^ 2 + (cos (2 * α) * cos β - sin (2 * α) * sin β) * (cos (2 * α) * cos β + sin (2 * α) * sin β) = 1 := by
    rw [eq5]
    have h3' : sin (2 * α) ^ 2 + cos (2 * α) ^ 2 = 1 := h3
    have h4' : sin β ^ 2 + cos β ^ 2 = 1 := h4
    have eq7 : sin (2 * α) ^ 2 + sin β ^ 2 + (cos (2 * α) ^ 2 * cos β ^ 2 - sin (2 * α) ^ 2 * sin β ^ 2) = 1 := by
      have eq8 : sin (2 * α) ^ 2 + cos (2 * α) ^ 2 = 1 := h3'
      have eq9 : sin β ^ 2 + cos β ^ 2 = 1 := h4'
      have eq10 : sin (2 * α) ^ 2 * (1 - sin β ^ 2) + sin β ^ 2 + cos (2 * α) ^ 2 * cos β ^ 2 = 1 := by
        rw [show 1 - sin β ^ 2 = cos β ^ 2 by linarith [eq9]]
        have eq11 : cos β ^ 2 * (sin (2 * α) ^ 2 + cos (2 * α) ^ 2) + sin β ^ 2 = 1 := by
          have eq12 : sin (2 * α) ^ 2 + cos (2 * α) ^ 2 = 1 := h3'
          rw [eq12] at *
          linarith [eq9]
        linarith [eq11]
      linarith
    linarith
  linarith [eq6]