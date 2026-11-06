import Mathlib

theorem algebra_241753 : √(13 + √(28 + √281)) * √(13 - √(28 + √281)) * √(141 + √281) = 140 := by

  have h1 : √(13 + √(28 + √281)) * √(13 - √(28 + √281)) = √(141 - √281) := by
    have h2 : (√(13 + √(28 + √281)) * √(13 - √(28 + √281))) ^ 2 = 141 - √281 := by
      have h3 : (√(13 + √(28 + √281)) * √(13 - √(28 + √281))) ^ 2 = (√(13 + √(28 + √281)))^2 * (√(13 - √(28 + √281)))^2 := by
        ring
      rw [h3]
      have h4 : (√(13 + √(28 + √281)))^2 = 13 + √(28 + √281) := by
        rw [Real.sq_sqrt]
        positivity
      have h5 : (√(13 - √(28 + √281)))^2 = 13 - √(28 + √281) := by
        rw [Real.sq_sqrt]
        have h6 : 0 ≤ (13 - √(28 + √281) : ℝ) := by
          have h7 : √(28 + √281) ≤ 13 := by
            nlinarith [Real.sqrt_nonneg (28 + √281), Real.sqrt_nonneg 281, Real.sq_sqrt (show (0 : ℝ) ≤ (28 + √281 : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (281 : ℝ) by positivity), show (28 + √281) ≤ (169 : ℝ) by nlinarith [Real.sqrt_nonneg (281 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (281 : ℝ) by positivity)]]
          linarith [show 0 ≤ 13 - √(28 + √281) from by linarith [h7]]
        linarith
      rw [h4, h5]
      nlinarith [Real.sqrt_nonneg (28 + √281), Real.sqrt_nonneg 281, Real.sq_sqrt (show (0 : ℝ) ≤ (28 + √281 : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (281 : ℝ) by positivity)]
    have h3 : √(13 + √(28 + √281)) * √(13 - √(28 + √281)) ≥ 0 := by
        positivity
    have h4 : √(141 - √281) ≥ 0 := by
        have h5 : √281 ≤ 141 := by 
            nlinarith [Real.sqrt_nonneg 281, Real.sq_sqrt (show (0 : ℝ) ≤ (281 : ℝ) by positivity), sq_nonneg (√281 - 141)]
        have h6 : 0 ≤ (141 - √281 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 281, h5]
        have h7 : √(141 - √281) ≥ 0 := by 
            positivity
        linarith [h7]
    have h7 : (√(13 + √(28 + √281)) * √(13 - √(28 + √281))) ^2 = (√(141 - √281)) ^2 := by
      rw [h2]
      have h7 : (√(141 - √281)) ^2 = (141 - √281) := by
        rw [Real.sq_sqrt]
        have h8 : 0 ≤ (141 - √281 : ℝ) := by
          have h77 : √281 ≤ 141 := by 
            nlinarith [Real.sqrt_nonneg 281, Real.sq_sqrt (show (0 : ℝ) ≤ (281 : ℝ) by positivity), sq_nonneg (√281 - 141)]
          linarith [h77, Real.sqrt_nonneg 281]
        linarith
      rw [h7]
    nlinarith [Real.sqrt_nonneg (141 - √281), Real.sqrt_nonneg (13 + √(28 + √281)), Real.sqrt_nonneg (13 - √(28 + √281))]
  have h3 : √(141 - √281) * √(141 + √281) = 140 := by
    have h4 : (√(141 - √281) * √(141 + √281)) ^ 2 = (140 : ℝ) ^2 := by
      calc
        (√(141 - √281) * √(141 + √281)) ^ 2 = (√(141 - √281)) ^ 2 * (√(141 + √281)) ^ 2 := by ring
        _ = (141 - √281) * (141 + √281) := by
          have h7 : (√(141 - √281)) ^ 2 = 141 - √281 := by
            rw [Real.sq_sqrt]
            have h8 : 0 ≤ (141 - √281 : ℝ) := by
              have h77 : √281 ≤ 141 := by 
                nlinarith [Real.sqrt_nonneg 281, Real.sq_sqrt (show (0 : ℝ) ≤ (281 : ℝ) by positivity), sq_nonneg (√281 - 141)]
              linarith [h77, Real.sqrt_nonneg 281]
            linarith
          have h8 : (√(141 + √281)) ^ 2 = 141 + √281 := by
            rw [Real.sq_sqrt]
            positivity
          rw [h7, h8]
        _ = (140 : ℝ) ^ 2 := by
          nlinarith [Real.sqrt_nonneg 281, Real.sq_sqrt (show (0 : ℝ) ≤ (281 : ℝ) by positivity)]
    have h3' : √(141 - √281) * √(141 + √281) ≥ 0 := by positivity
    have h4' : (140 : ℝ) ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg (141 - √281), Real.sqrt_nonneg (141 + √281)]
  calc
    √(13 + √(28 + √281)) * √(13 - √(28 + √281)) * √(141 + √281)
        = (√(13 + √(28 + √281)) * √(13 - √(28 + √281))) * √(141 + √281) := by ring
    _ = √(141 - √281) * √(141 + √281) := by rw [h1]
    _ = 140 := by linarith [h3]