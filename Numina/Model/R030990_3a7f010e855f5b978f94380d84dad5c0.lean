import Mathlib

open BigOperators Real Set


theorem algebra_183297 {x : ℝ} (hx : 2 * x - 1 ≥ 0) :
    sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = sqrt 2 ↔
    1 / 2 ≤ x ∧ x ≤ 1 := by
  constructor
  · -- Forward implication: if sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = sqrt 2, then 1/2 ≤ x ≤ 1
    intro h_eq
    have hx1 : 1 / 2 ≤ x := by nlinarith
    have h1 : (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1))) ^ 2 = (sqrt 2) ^ 2 := by
      rw [h_eq]
    have h2 : (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1))) ^ 2 =
        (sqrt (x + sqrt (2 * x - 1))) ^ 2 + (sqrt (x - sqrt (2 * x - 1))) ^ 2 + 2 * (sqrt (x + sqrt (2 * x - 1)) * sqrt (x - sqrt (2 * x - 1))) := by ring
    have hx2 : 0 ≤ x + sqrt (2 * x - 1) := by
      nlinarith [Real.sqrt_nonneg (2 * x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x - 1 by linarith)]
    have hx3 : 0 ≤ x - sqrt (2 * x - 1) := by
      nlinarith [Real.sqrt_nonneg (2 * x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x - 1 by linarith),
        sq_nonneg (x - 1), sq_nonneg (Real.sqrt (2 * x - 1) - (x - 1)), sq_nonneg (x - Real.sqrt (2 * x - 1))]
    have h3 : (sqrt (x + sqrt (2 * x - 1))) ^ 2 = x + sqrt (2 * x - 1) := by
      rw [Real.sq_sqrt]
      linarith
    have h4 : (sqrt (x - sqrt (2 * x - 1))) ^ 2 = x - sqrt (2 * x - 1) := by
      rw [Real.sq_sqrt]
      nlinarith
    have h5 : 2 * (sqrt (x + sqrt (2 * x - 1)) * sqrt (x - sqrt (2 * x - 1))) = 2 * abs (x - 1) := by
      have h8 : sqrt (x + sqrt (2 * x - 1)) * sqrt (x - sqrt (2 * x - 1)) = abs (x - 1) := by
        have h10 : sqrt (x + sqrt (2 * x - 1)) * sqrt (x - sqrt (2 * x - 1)) = sqrt ((x + sqrt (2 * x - 1)) * (x - sqrt (2 * x - 1))) := by
          rw [← Real.sqrt_mul (by
            have h70 : x + sqrt (2 * x - 1) ≥ 0 := by
              nlinarith [Real.sqrt_nonneg (2 * x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x - 1 by linarith)]
            nlinarith
          )
          ]
        have h11 : (x + sqrt (2 * x - 1)) * (x - sqrt (2 * x - 1)) = (x - 1) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (2 * x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x - 1 by linarith)
          ]
        have h12 : sqrt ((x + sqrt (2 * x - 1)) * (x - sqrt (2 * x - 1))) = abs (x - 1) := by
          rw [h11]
          rw [Real.sqrt_sq_eq_abs]
        rw [h10, h12]
      linarith [h8]
    have h6 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith)
    rw [h2, h3, h4, h5, h6] at h1
    have hx4 : x ≤ 1 := by
      cases' abs_cases (x - 1) with h10 h10
      · -- case |x - 1| = x - 1
        nlinarith
      · -- case |x - 1| = 1 - x
        nlinarith
    constructor
    · linarith
    · linarith
  · -- Backward implication: if 1/2 ≤ x ≤ 1, then sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = sqrt 2
    rintro ⟨hx1, hx2⟩
    have h1 : (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1))) ^ 2 = 2 := by
      have h2 : (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1))) ^ 2 =
          (sqrt (x + sqrt (2 * x - 1))) ^ 2 + (sqrt (x - sqrt (2 * x - 1))) ^ 2 + 2 * (sqrt (x + sqrt (2 * x - 1)) * sqrt (x - sqrt (2 * x - 1))) := by ring
      have hx2 : 0 ≤ x + sqrt (2 * x - 1) := by
        nlinarith [Real.sqrt_nonneg (2 * x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x - 1 by linarith)]
      have hx3 : 0 ≤ x - sqrt (2 * x - 1) := by
        nlinarith [Real.sqrt_nonneg (2 * x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x - 1 by linarith),
          sq_nonneg (x - 1), sq_nonneg (Real.sqrt (2 * x - 1) - (x - 1)), sq_nonneg (x - Real.sqrt (2 * x - 1))]
      have h3 : (sqrt (x + sqrt (2 * x - 1))) ^ 2 = x + sqrt (2 * x - 1) := by
        rw [Real.sq_sqrt]
        linarith
      have h4 : (sqrt (x - sqrt (2 * x - 1))) ^ 2 = x - sqrt (2 * x - 1) := by
        rw [Real.sq_sqrt]
        nlinarith
      have h5 : 2 * (sqrt (x + sqrt (2 * x - 1)) * sqrt (x - sqrt (2 * x - 1))) = 2 * abs (x - 1) := by
        have h8 : sqrt (x + sqrt (2 * x - 1)) * sqrt (x - sqrt (2 * x - 1)) = abs (x - 1) := by
          have h10 : sqrt (x + sqrt (2 * x - 1)) * sqrt (x - sqrt (2 * x - 1)) = sqrt ((x + sqrt (2 * x - 1)) * (x - sqrt (2 * x - 1))) := by
            rw [← Real.sqrt_mul (by
              have h70 : x + sqrt (2 * x - 1) ≥ 0 := by
                nlinarith [Real.sqrt_nonneg (2 * x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x - 1 by linarith)]
              nlinarith
            )
            ]
          have h11 : (x + sqrt (2 * x - 1)) * (x - sqrt (2 * x - 1)) = (x - 1) ^ 2 := by
            nlinarith [Real.sqrt_nonneg (2 * x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x - 1 by linarith)
            ]
          have h12 : sqrt ((x + sqrt (2 * x - 1)) * (x - sqrt (2 * x - 1))) = abs (x - 1) := by
            rw [h11]
            rw [Real.sqrt_sq_eq_abs]
          rw [h10, h12]
        linarith [h8]
      have h7 : abs (x - 1) = 1 - x := by
        rw [abs_of_nonpos (by linarith)]
        all_goals nlinarith
      rw [h2, h3, h4, h5, h7]
      nlinarith [Real.sqrt_nonneg (2 * x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x - 1 by linarith)]
    have h3 : sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) ≥ 0 := by
      positivity
    have h4 : sqrt 2 ≥ 0 := by positivity
    have h5 : sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith), Real.sqrt_nonneg (2 * x - 1)]
    linarith