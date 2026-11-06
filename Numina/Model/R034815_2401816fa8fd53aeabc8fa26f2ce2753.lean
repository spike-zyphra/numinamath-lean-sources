import Mathlib

theorem algebra_257448 : Real.sqrt (2 + Real.sqrt 3) * ((Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2) ^ ((1 : ℝ) / 3) = 1 := by
  have h1 : 0 ≤ 2 + Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

  have h3 : 0 ≤ (Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
        mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3)]

  have h5 : Real.sqrt (2 + Real.sqrt 3) ^ 2 = 2 + Real.sqrt 3 := by
    rw [Real.sq_sqrt]
    linarith
  have h61 : Real.sqrt (2 + Real.sqrt 3) ^ 3 = Real.sqrt (2 + Real.sqrt 3) * (2 + Real.sqrt 3) := by
    calc
      Real.sqrt (2 + Real.sqrt 3) ^ 3 = Real.sqrt (2 + Real.sqrt 3) * Real.sqrt (2 + Real.sqrt 3) ^ 2 := by ring
      _ = Real.sqrt (2 + Real.sqrt 3) * (2 + Real.sqrt 3) := by rw [h5]

  have h81 : (( (Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2 ) ^ ((1 : ℝ) / 3) ) ^ 3
          = ( (Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2 ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals nlinarith
  
  have h62 : (Real.sqrt (2 + Real.sqrt 3) * ((Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2) ^ ((1 : ℝ) / 3) ) ^ 3 =
      Real.sqrt (2 + Real.sqrt 3) ^ 3 * (( (Real.sqrt 2 * (3 * Real.sqrt 3 - 5) ) / 2 ) ^ ((1 : ℝ) / 3) ) ^ 3 := by
    ring_nf
  
  have h631 : Real.sqrt (2 + Real.sqrt 3) ^ 3 * (( (Real.sqrt 2 * (3 * Real.sqrt 3 - 5) ) / 2 ) ^ ((1 : ℝ) / 3) ) ^ 3 = 1 := by 
    rw [h81]
    have h711 : Real.sqrt (2 + Real.sqrt 3) ^ 3 = Real.sqrt (2 + Real.sqrt 3) * (2 + Real.sqrt 3) := h61
    rw [h711]
    -- Now prove: Real.sqrt (2 + Real.sqrt 3) * (2 + Real.sqrt 3) * ( (Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2 ) = 1
    have h700 : Real.sqrt (2 + Real.sqrt 3) * (2 + Real.sqrt 3) * ( (Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2 ) = 1 := by
      have h111 : (Real.sqrt (2 + Real.sqrt 3) * (2 + Real.sqrt 3) * ( (Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2 ) ) ^ 2 = 1 := by
        calc 
          (Real.sqrt (2 + Real.sqrt 3) * (2 + Real.sqrt 3) * ( (Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2 ) ) ^ 2
          _ = (Real.sqrt (2 + Real.sqrt 3) ^ 2) * ( (2 + Real.sqrt 3) ^ 2 ) * ( ( (Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2 ) ^ 2 ) := by 
            ring_nf
          _ = (2 + Real.sqrt 3) * ( (2 + Real.sqrt 3) ^ 2 ) * ( ( (Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2 ) ^ 2 ) := by 
            rw [h5]
          _ = (2 + Real.sqrt 3) * ( (2 + Real.sqrt 3) ^ 2 ) * ( (Real.sqrt 2 ^ 2 * (3 * Real.sqrt 3 - 5) ^ 2 ) / 4 ) := by
            ring_nf
            <;> field_simp <;> ring_nf
          _ = (2 + Real.sqrt 3) * ( (2 + Real.sqrt 3) ^ 2 ) * ( (2 * (52 - 30 * Real.sqrt 3)) / 4 ) := by
            have h551 : Real.sqrt 2 ^ 2 = (2 : ℝ) := by 
              rw [Real.sq_sqrt]
              linarith
            have h444 : (3 * Real.sqrt 3 - 5) ^ 2 = 52 - 30 * Real.sqrt 3 := by 
              nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
            rw [h551, h444]
            <;> ring_nf <;> norm_num
            <;> ring_nf <;> norm_num
          _ = 1 := by
            nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (3 : ℝ))]
      have h112 : Real.sqrt (2 + Real.sqrt 3) * (2 + Real.sqrt 3) * ( (Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2 ) ≥ 0 := by
        positivity
      nlinarith
    linarith
  
  have h51 : (Real.sqrt (2 + Real.sqrt 3) * ((Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2) ^ ((1 : ℝ) / 3) ) ^ 3 = 1 := by
    nlinarith [h62, h631]

  have h91 : Real.sqrt (2 + Real.sqrt 3) * ((Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2) ^ ((1 : ℝ) / 3) ≥ 0 := by
    positivity

  have h91' : Real.sqrt (2 + Real.sqrt 3) * ((Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2) ^ ((1 : ℝ) / 3) = 1 := by
    have h52 : (Real.sqrt (2 + Real.sqrt 3) * ((Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2) ^ ((1 : ℝ) / 3) ) ^ 3 = 1 := h51
    have h911 : Real.sqrt (2 + Real.sqrt 3) * ((Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2) ^ ((1 : ℝ) / 3) ≥ 0 := h91

    have h53 : Real.sqrt (2 + Real.sqrt 3) * ((Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2) ^ ((1 : ℝ) / 3) = 1 := by
      have h54 : (Real.sqrt (2 + Real.sqrt 3) * ((Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2) ^ ((1 : ℝ) / 3) ) ^ 3 - 1 = 0 := by
        linarith 
      have h55 : (Real.sqrt (2 + Real.sqrt 3) * ((Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2) ^ ((1 : ℝ) / 3) ) ^ 3 - 1 = 
          (Real.sqrt (2 + Real.sqrt 3) * ((Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2) ^ ((1 : ℝ) / 3) - 1 ) * 
            ( (Real.sqrt (2 + Real.sqrt 3) * ((Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2) ^ ((1 : ℝ) / 3) ) ^ 2 + 
                (Real.sqrt (2 + Real.sqrt 3) * ((Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2) ^ ((1 : ℝ) / 3) ) + 1 ) := by 
        ring_nf
      rw [h55] at h54
      cases' (mul_eq_zero.1 h54) with h56 h57
      · -- Case $A - 1 = 0$
        linarith
      · -- The quadratic is zero
        nlinarith [sq_nonneg ( (Real.sqrt (2 + Real.sqrt 3) * ((Real.sqrt 2 * (3 * Real.sqrt 3 - 5)) / 2) ^ ((1 : ℝ) / 3) ) - 1 ) ]
    exact h53

  linarith