import Mathlib

theorem algebra_145855 (z : ℂ) (hz : z = (-(1 - Complex.I) / Real.sqrt 2)) :
    z^100 + z^50 + 1 = -Complex.I := by
  rw [hz]
  have h1 : ((-(1 - Complex.I) / Real.sqrt 2) : ℂ) ^ 2 = -Complex.I := by
    simp [pow_two, Complex.ext_iff,Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
          Complex.I_re, Complex.I_im, mul_add, mul_comm, mul_assoc, pow_two]
    field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), 
                  Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr, mul_add, mul_comm, mul_assoc]
    <;> ring
  have h2 : ((-(1 - Complex.I) / Real.sqrt 2) : ℂ) ^ 50 = -Complex.I := by
    have h3 : ((-(1 - Complex.I) / Real.sqrt 2) : ℂ) ^ 2 = -Complex.I := h1
    calc
      ((-(1 - Complex.I) / Real.sqrt 2) : ℂ) ^ 50 = (((-(1 - Complex.I) / Real.sqrt 2) : ℂ) ^ 2) ^ 25 := by 
        ring_nf
      _ = (-Complex.I) ^ 25 := by 
        rw [h3]
      _ = -Complex.I := by 
        have h4 : (-Complex.I) ^ 2 = -1 := by 
          calc
            (-Complex.I) ^ 2 = (Complex.I) ^ 2 := by 
              ring_nf
            _ = -1 := by 
              simp [Complex.I_sq]
        calc
          (-Complex.I) ^ 25 = (-Complex.I) ^ 24 * (-Complex.I) := by 
            ring
          _ = ((-Complex.I) ^ 2) ^ 12 * (-Complex.I) := by 
            ring
          _ = (-1) ^ 12 * (-Complex.I) := by 
            rw [h4]
          _ = (1) * (-Complex.I) := by 
            norm_num
          _ = -Complex.I := by 
            ring
  have h5 : ((-(1 - Complex.I) / Real.sqrt 2) : ℂ) ^ 100 = -1 := by 
    calc 
      ((-(1 - Complex.I) / Real.sqrt 2) : ℂ) ^ 100 = (((-(1 - Complex.I) / Real.sqrt 2) : ℂ) ^ 50) ^ 2 := by 
        ring_nf
      _ = (-Complex.I) ^ 2 := by 
        rw [h2]
      _ = -1 := by 
        simp [Complex.I_sq]
  rw [h5, h2]
  ring_nf
  <;> norm_num [Complex.ext_iff]
  <;> try { tauto }
  <;> ring_nf
  <;> norm_num
  <;> try { tauto }
  <;> ring