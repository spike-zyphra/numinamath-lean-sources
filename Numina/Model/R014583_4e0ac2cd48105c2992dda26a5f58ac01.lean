import Mathlib

theorem algebra_163833 (a n m : ℝ) :
    Real.cos (n * a / 2) ^ 2 - Real.sin (m * a / 2) ^ 2 =
    Real.cos ((n + m) * a / 2) * Real.cos ((-n + m) * a / 2) := by

  have h1 : Real.cos (n * a / 2) ^ 2 = (1 + Real.cos (n * a)) / 2 := by
    have h4 : Real.cos (n * a / 2) ^ 2 = (1 + Real.cos (2 * (n * a / 2)) ) / 2 := by
      rw [Real.cos_sq]
      ring_nf
    have h5 : 2 * (n * a / 2) = n * a := by
      ring_nf
    rw [h5] at h4
    linarith

  have h2 : Real.sin (m * a / 2) ^ 2 = (1 - Real.cos (m * a)) / 2 := by
    have h5 : Real.sin (m * a / 2) ^ 2 = (1 - Real.cos (2 * (m * a / 2)) ) / 2 := by
      rw [Real.sin_sq_eq_half_sub]
      ring_nf
    have h6 : 2 * (m * a / 2) = m * a := by
      ring_nf
    rw [h6] at h5
    linarith

  have eq1 : Real.cos (n * a / 2) ^ 2 - Real.sin (m * a / 2) ^ 2 = (Real.cos (n * a) + Real.cos (m * a)) / 2 := by
    rw [h1, h2]
    ring_nf

  have eq2 : Real.cos ((n + m) * a / 2) * Real.cos ((-n + m) * a / 2) = (Real.cos (n * a) + Real.cos (m * a)) / 2 := by

    have h4 : Real.cos ((n + m) * a / 2) * Real.cos ((-n + m) * a / 2) =
      (Real.cos (( (n + m) * a / 2 + (-n + m) * a / 2 )) + Real.cos (( (n + m) * a / 2 - (-n + m) * a / 2 )) ) / 2 := by 
      rw [Real.cos_add_cos]
      <;> ring_nf

    have h5 : ( (n + m) * a / 2 + (-n + m) * a / 2 ) = m * a := by
      ring_nf

    have h6 : ( (n + m) * a / 2 - (-n + m) * a / 2 ) = n * a := by
      ring_nf

    rw [h4, h5, h6]
    <;> ring_nf

  rw [eq1, eq2]