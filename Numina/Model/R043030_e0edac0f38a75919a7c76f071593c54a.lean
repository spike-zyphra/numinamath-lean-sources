import Mathlib

theorem algebra_20855 :
    IsLeast {d : ℝ | ∃ x y : ℝ, x ≠ 0 ∧ y ≠ 0 ∧ x * y * (x ^ 2 - y ^ 2) = x ^ 2 + y ^ 2 ∧ d = x ^ 2 + y ^ 2} 4 := by
  constructor
  · -- Show 4 is in the set
    use Real.sqrt (2 + Real.sqrt 2), Real.sqrt (2 - Real.sqrt 2)
    constructor
    · -- Show x ≠ 0
      have h1 : Real.sqrt (2 + Real.sqrt 2) > 0 := by
        apply Real.sqrt_pos.mpr
        have h2 : 2 + Real.sqrt 2 > 0 := by
          have h4 : Real.sqrt 2 > 0 := by
            apply Real.sqrt_pos.mpr
            all_goals linarith
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith)]
        linarith
      linarith
    constructor
    · -- Show y ≠ 0
      have h1 : Real.sqrt (2 - Real.sqrt 2) > 0 := by
        apply Real.sqrt_pos.mpr
        have h1 : 2 - Real.sqrt 2 > 0 := by
          have h2 : Real.sqrt 2 < (2 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith)]
          linarith
        linarith
      linarith
    constructor
    · -- Show x * y * (x ^ 2 - y ^ 2) = x ^ 2 + y ^ 2
      have h3 : Real.sqrt (2 + Real.sqrt 2) * Real.sqrt (2 - Real.sqrt 2) = Real.sqrt 2 := by
        have h11 : Real.sqrt (2 + Real.sqrt 2) * Real.sqrt (2 - Real.sqrt 2) = Real.sqrt ((2 + Real.sqrt 2) * (2 - Real.sqrt 2)) := by
          rw [← Real.sqrt_mul (by
            have h4 : 2 + Real.sqrt 2 ≥ 0 := by
              have h4 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith)]
            have h7 : 2 - Real.sqrt 2 ≥ 0 := by
              have h2 : Real.sqrt 2 ≤ (2 : ℝ) := by
                nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith)]
              linarith
            all_goals nlinarith [Real.sqrt_nonneg (2 + Real.sqrt 2), Real.sqrt_nonneg (2 - Real.sqrt 2)]
          )]
        rw [h11]
        have h15 : (2 + Real.sqrt 2) * (2 - Real.sqrt 2) = (2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith)]
        rw [h15]
        all_goals
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith)]
      have h4 : (Real.sqrt (2 + Real.sqrt 2) : ℝ) ^ 2 = 2 + Real.sqrt 2 := by
        rw [Real.sq_sqrt]
        have h4 : 2 + Real.sqrt 2 ≥ 0 := by
          have h4 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith)]
        linarith
      have h5 : (Real.sqrt (2 - Real.sqrt 2) : ℝ) ^ 2 = 2 - Real.sqrt 2 := by
        rw [Real.sq_sqrt]
        have h1 : 2 - Real.sqrt 2 ≥ 0 := by
          have h2 : Real.sqrt 2 ≤ (2 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith)]
          linarith
        linarith
      nlinarith [h3, h4, h5, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith)]
    · -- Show 4 = x^2 + y^2
      have h4 : (Real.sqrt (2 + Real.sqrt 2) : ℝ) ^ 2 = 2 + Real.sqrt 2 := by
        rw [Real.sq_sqrt]
        have h4 : 2 + Real.sqrt 2 ≥ 0 := by
          have h4 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith)]
        linarith
      have h5 : (Real.sqrt (2 - Real.sqrt 2) : ℝ) ^ 2 = 2 - Real.sqrt 2 := by
        rw [Real.sq_sqrt]
        have h1 : 2 - Real.sqrt 2 ≥ 0 := by
          have h2 : Real.sqrt 2 ≤ (2 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith)]
          linarith
        linarith
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith)]
  · -- Show 4 is the minimum element
    intro d hd
    rcases hd with ⟨x, y, hx, hy, h_eq, heq⟩
    have h3 : x ^ 2 + y ^ 2 ≥ 4 := by
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), sq_nonneg (x ^ 2 - 2 * x * y - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2 - 2 * x * y), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 2 - y ^ 2 - 2 * (x * y)), sq_nonneg (x ^ 2 - y ^ 2 + 2 * (x * y)), sq_pos_of_ne_zero (show x ^ 2 ≠ 0 by
        have h0 : x ^ 2 ≠ 0 := by
          intro h
          have h1 : x = 0 := by
            nlinarith
          tauto
        assumption
      ), sq_pos_of_ne_zero (show y ^ 2 ≠ 0 by
        have h0 : y ^ 2 ≠ 0 := by
          intro h
          have h1 : y = 0 := by
            nlinarith
          tauto
        assumption
      ), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y)]
    nlinarith