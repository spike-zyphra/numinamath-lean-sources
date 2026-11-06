import Mathlib

open Real

theorem algebra_105162 {x : Fin 2 → ℝ} (hx : ∀ i, 0 ≤ x i) (hxi : x 0 ≥ x 1)
    (hsum : x 0 + x 1 = 2) :
    sqrt (x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2)) + sqrt (x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2)) = 2 := by

  have h1 : x 1 ≤ x 0 := by linarith [hxi]
  have h2 : x 1 ≥ 0 := by exact hx 1
  have h3 : x 0 ≥ 0 := by exact hx 0
  
  have h4 : x 0 ^ 2 - x 1 ^ 2 = (x 0 + x 1) * (x 0 - x 1) := by
    ring_nf
  
  have h5 : x 0 ^ 2 - x 1 ^ 2 = 2 * (x 0 - x 1) := by 
    rw [h4]
    rw [hsum]

  have h7 : (sqrt (x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2)) + sqrt (x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2))) ^ 2 = 4 := by

    have h8 : (sqrt (x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2)) + sqrt (x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2))) ^ 2 =
        (sqrt (x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2))) ^ 2 + (sqrt (x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2))) ^ 2 + 2 * (sqrt (x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2)) * sqrt (x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2)) ) := by ring

    have h9 : (sqrt (x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2))) ^ 2 = x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2) := by 
      rw [Real.sq_sqrt]
      have h10 : x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2) ≥ 0 := by
        positivity
      linarith

    have h11 : (sqrt (x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2))) ^ 2 = x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2) := by 
      rw [Real.sq_sqrt]
      have h12 : x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2) ≥ 0 := by 
        have h13 : sqrt (x 0 ^ 2 - x 1 ^ 2) ≤ x 0 := by 
          have h14 : (sqrt (x 0 ^ 2 - x 1 ^ 2)) ^ 2 ≤ (x 0) ^ 2 := by 
            have h15 : (sqrt (x 0 ^ 2 - x 1 ^ 2)) ^ 2 = x 0 ^ 2 - x 1 ^ 2 := by 
              rw [Real.sq_sqrt]
              have h16 : x 0 ^ 2 - x 1 ^ 2 ≥ 0 := by 
                nlinarith [hsum, hxi, hx 0, hx 1]
              linarith
            nlinarith [h15, hsum, h2, h3]
          nlinarith [Real.sqrt_nonneg (x 0 ^ 2 - x 1 ^ 2), h3]
        nlinarith [Real.sqrt_nonneg (x 0 ^ 2 - x 1 ^ 2), h3]
      linarith

    have h17 : sqrt (x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2)) * sqrt (x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2)) = x 1 := by 
      have h18 : sqrt (x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2)) * sqrt (x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2)) = sqrt ((x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2)) * (x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2)) ) := by 
        rw [← Real.sqrt_mul (by positivity)]
      have h19 : (x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2)) * (x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2)) = x 1 ^ 2 := by 
        nlinarith [Real.sq_sqrt (show x 0 ^ 2 - x 1 ^ 2 ≥ 0 by nlinarith [hsum, hxi, hx 0, hx 1] ), hsum, hx 0, hx 1, Real.sqrt_nonneg (x 0 ^ 2 - x 1 ^ 2)]
      rw [h18, h19]
      have h20 : sqrt (x 1 ^ 2) = x 1 := by 
        rw [Real.sqrt_sq (by linarith [hx 1]) ]
      rw [h20]

    rw [h8, h9, h11, h17]
    nlinarith [hsum, hx 0, hx 1, Real.sqrt_nonneg (x 0 ^ 2 - x 1 ^ 2), Real.sqrt_nonneg (x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2)), Real.sqrt_nonneg (x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2)) ]

  have h6 : sqrt (x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2)) + sqrt (x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2)) ≥ 0 := by 
    positivity

  have h8 : sqrt (x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2)) + sqrt (x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2)) = 2 := by 
    nlinarith [h7, h6, Real.sqrt_nonneg (x 0 + sqrt (x 0 ^ 2 - x 1 ^ 2)), Real.sqrt_nonneg (x 0 - sqrt (x 0 ^ 2 - x 1 ^ 2)) ]

  exact h8