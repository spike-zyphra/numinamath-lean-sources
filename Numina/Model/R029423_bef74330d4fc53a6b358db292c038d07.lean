import Mathlib

theorem algebra_640 (x : ℝ) : (Real.sin x)^6 + (Real.cos x)^6 = Real.sin (2 * x) ↔
    Real.sin (2 * x) = 2 / 3 := by
  constructor
  · -- Assume (Real.sin x)^6 + (Real.cos x)^6 = Real.sin (2 * x), prove Real.sin (2 * x) = 2 / 3
    intro h
    have h1 : (Real.sin x) ^ 2 + (Real.cos x) ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h2 : (Real.sin x) ^ 6 + (Real.cos x) ^ 6 = ((Real.sin x) ^ 2 + (Real.cos x) ^ 2) ^ 3 - 3 * ((Real.sin x) ^ 2) * ((Real.cos x) ^ 2) * ((Real.sin x) ^ 2 + (Real.cos x) ^ 2) := by
      ring
    have h3 : (Real.sin x) ^ 6 + (Real.cos x) ^ 6 = 1 - 3 * Real.sin x ^ 2 * Real.cos x ^ 2 := by
      rw [h2, h1]
      ring
    have h4 : Real.sin x ^ 2 * Real.cos x ^ 2 = (Real.sin (2 * x) / 2) ^ 2 := by 
      have h5 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by 
        rw [Real.sin_two_mul]
      have h6 : (Real.sin x) * (Real.cos x) = Real.sin (2 * x) / 2 := by 
        linarith [h5]
      calc
        Real.sin x ^ 2 * Real.cos x ^ 2 = ((Real.sin x) * (Real.cos x)) ^ 2 := by ring
        _ = (Real.sin (2 * x) / 2) ^ 2 := by rw [h6]
    have eq3 : 3 * Real.sin x ^ 2 * Real.cos x ^ 2 = 3 * (Real.sin (2 * x) / 2) ^ 2 := by
      have eq4 : Real.sin x ^ 2 * Real.cos x ^ 2 = (Real.sin (2 * x) / 2) ^ 2 := h4
      linarith [eq4]
    have eq4 : 1 - 3 * Real.sin x ^ 2 * Real.cos x ^ 2 = 1 - 3 * (Real.sin (2 * x) / 2) ^ 2 := by
      nlinarith [eq3]
    have h5_rw : (Real.sin x) ^ 6 + (Real.cos x) ^ 6 = 1 - 3 * (Real.sin (2 * x) / 2) ^ 2 := by
      linarith [h3, eq4]
    rw [h5_rw] at h
    have h6 : 3 * (Real.sin (2 * x) ) ^ 2 + 4 * (Real.sin (2 * x) ) - 4 = 0 := by
      nlinarith [h]
    have h7 : Real.sin (2 * x) = 2 / 3 := by
      have h8 : 3 * (Real.sin (2 * x) ) ^ 2 + 4 * (Real.sin (2 * x) ) - 4 = 0 := h6
      have h9 : Real.sin (2 * x) ^ 2 ≤ 1 := by 
        apply Real.sin_sq_le_one
      have h10 : (Real.sin (2 * x) - 2 / 3) * (Real.sin (2 * x) + 2 ) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h10) with h11 h12
      · -- sin(2x) - 2/3 = 0
        linarith
      · -- sin(2x) + 2 = 0
        have h12' : Real.sin (2 * x) = -2 := by linarith
        nlinarith [Real.sin_le_one (2 * x), Real.neg_one_le_sin (2 * x)]
    linarith
  · -- Assume Real.sin (2 * x) = 2 / 3, prove (Real.sin x)^6 + (Real.cos x)^6 = Real.sin (2 * x)
    intro h
    have h1 : (Real.sin x) ^ 2 + (Real.cos x) ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h2 : (Real.sin x) ^ 6 + (Real.cos x) ^ 6 = ((Real.sin x) ^ 2 + (Real.cos x) ^ 2) ^ 3 - 3 * ((Real.sin x) ^ 2) * ((Real.cos x) ^ 2) * ((Real.sin x) ^ 2 + (Real.cos x) ^ 2) := by
      ring
    have h3 : (Real.sin x) ^ 6 + (Real.cos x) ^ 6 = 1 - 3 * Real.sin x ^ 2 * Real.cos x ^ 2 := by
      rw [h2, h1]
      ring
    have h4 : Real.sin x ^ 2 * Real.cos x ^ 2 = (Real.sin (2 * x) / 2) ^ 2 := by 
      have h5 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by 
        rw [Real.sin_two_mul]
      have h6 : (Real.sin x) * (Real.cos x) = Real.sin (2 * x) / 2 := by 
        linarith [h5]
      calc
        Real.sin x ^ 2 * Real.cos x ^ 2 = ((Real.sin x) * (Real.cos x)) ^ 2 := by ring
        _ = (Real.sin (2 * x) / 2) ^ 2 := by rw [h6]
    have eq3 : 3 * Real.sin x ^ 2 * Real.cos x ^ 2 = 3 * (Real.sin (2 * x) / 2) ^ 2 := by
      have eq4 : Real.sin x ^ 2 * Real.cos x ^ 2 = (Real.sin (2 * x) / 2) ^ 2 := h4
      linarith [eq4]
    have eq4 : 1 - 3 * Real.sin x ^ 2 * Real.cos x ^ 2 = 1 - 3 * (Real.sin (2 * x) / 2) ^ 2 := by
      nlinarith [eq3]
    have h5_rw : (Real.sin x) ^ 6 + (Real.cos x) ^ 6 = 1 - 3 * (Real.sin (2 * x) / 2) ^ 2 := by
      linarith [h3, eq4]
    rw [h5_rw]
    nlinarith [h]