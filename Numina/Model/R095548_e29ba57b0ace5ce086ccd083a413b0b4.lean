import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_122657 {x : ℝ} (hx : 0 ≤ 2 * x - 1) :
    (x + sqrt (2 * x - 1)) ≥ 0 ∧ (x - sqrt (2 * x - 1)) ≥ 0 ∧
    sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = sqrt 2 ↔
    x ∈ Icc (1 / 2) 1 := by

  constructor
  · -- Forward direction: equation holds → x ∈ [1/2, 1]
    rintro ⟨h1, h2, heq⟩
    have y_nonneg : 0 ≤ Real.sqrt (2 * x - 1) := by positivity

    have h3 : (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1))) ^ 2 = (sqrt 2) ^ 2 := by
      rw [heq]

    have h4 : (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1))) ^ 2 = (sqrt (x + sqrt (2 * x - 1))) ^ 2 + (sqrt (x - sqrt (2 * x - 1))) ^ 2 + 2 * (sqrt (x + sqrt (2 * x - 1)) * sqrt (x - sqrt (2 * x - 1))) := by ring
    have h5 : (sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    rw [h4] at h3
    rw [h5] at h3

    have h6 : (Real.sqrt (x + Real.sqrt (2 * x - 1))) ^ 2 = x + Real.sqrt (2 * x - 1) := by
      exact Real.sq_sqrt (show 0 ≤ x + Real.sqrt (2 * x - 1) by linarith [Real.sqrt_nonneg (2 * x - 1), Real.sqrt_nonneg (2 * x - 1), h1])

    have h7 : (Real.sqrt (x - Real.sqrt (2 * x - 1))) ^ 2 = x - Real.sqrt (2 * x - 1) := by
      exact Real.sq_sqrt (show 0 ≤ x - Real.sqrt (2 * x - 1) by linarith [Real.sqrt_nonneg (2 * x - 1), Real.sqrt_nonneg (2 * x - 1), h2])

    have h8 : Real.sqrt (x + Real.sqrt (2 * x - 1)) * Real.sqrt (x - Real.sqrt (2 * x - 1)) = Real.sqrt ((x + Real.sqrt (2 * x - 1)) * (x - Real.sqrt (2 * x - 1))) := by
      rw [← Real.sqrt_mul (by positivity)]

    have h9 : (x + Real.sqrt (2 * x - 1)) * (x - Real.sqrt (2 * x - 1)) = x ^ 2 - (Real.sqrt (2 * x - 1)) ^ 2 := by
      ring

    have h10 : Real.sqrt ((x + Real.sqrt (2 * x - 1)) * (x - Real.sqrt (2 * x - 1))) = Real.sqrt (x^2 - (Real.sqrt (2 * x - 1)) ^ 2) := by
      rw [h9]

    have h11 : (Real.sqrt (2 * x - 1)) ^ 2 = 2 * x - 1 := by
      exact Real.sq_sqrt (show 0 ≤ 2 * x - 1 by linarith)

    rw [h8, h10] at h3
    rw [h6, h7, h11] at h3

    have h12 : x + Real.sqrt (2 * x - 1) + (x - Real.sqrt (2 * x - 1)) + 2 * Real.sqrt (x^2 - (2 * x - 1)) = 2 := by
      linarith

    have h13 : x^2 - (2 * x - 1) = (x - 1)^2 := by ring

    have h14 : Real.sqrt (x^2 - (2 * x - 1)) = abs (x - 1) := by
      rw [h13]
      have h15 : Real.sqrt ((x - 1) ^ 2) = abs (x - 1) := by
        rw [Real.sqrt_sq_eq_abs]
      exact h15

    rw [h14] at h12

    by_cases h14 : x - 1 ≥ 0
    · -- Case where x ≥ 1
      rw [abs_of_nonneg h14] at h12
      have hx2 : x = 1 := by nlinarith
      exact ⟨by nlinarith, by nlinarith⟩

    · -- Case where x < 1
      rw [abs_of_neg (show x - 1 < 0 by linarith)] at h12
      constructor
      · -- x ≥ 1/2
        linarith
      · -- x ≤ 1
        linarith

  · -- Reverse direction: x ∈ [1/2, 1] implies the equation
    rintro ⟨hx1, hx2⟩
    have hx3 : 0 ≤ 2 * x - 1 := by linarith

    have h21 : sqrt (2 * x - 1) ≥ 0 := Real.sqrt_nonneg (2 * x - 1)

    have h22 : x + sqrt (2 * x - 1) ≥ 0 := by nlinarith

    have h23 : x - sqrt (2 * x - 1) ≥ 0 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 * x - 1 by linarith), Real.sqrt_nonneg (2 * x - 1)]

    constructor
    · linarith

    constructor
    · linarith

    · -- Prove the equation
      have h24 : sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1)) = sqrt 2 := by
        have h25 : (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1))) ^ 2 = (sqrt 2) ^ 2 := by
          have h26 : (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1))) ^ 2 = (sqrt (x + sqrt (2 * x - 1))) ^ 2 + (sqrt (x - sqrt (2 * x - 1))) ^ 2 + 2 * (sqrt (x + sqrt (2 * x - 1)) * sqrt (x - sqrt (2 * x - 1))) := by ring
          have h27 : (sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
          rw [h26, h27]

          have h28 : (sqrt (x + sqrt (2 * x - 1))) ^ 2 = x + sqrt (2 * x - 1) := by
            exact Real.sq_sqrt (show 0 ≤ x + Real.sqrt (2 * x - 1) by linarith [Real.sqrt_nonneg (2 * x - 1), Real.sqrt_nonneg (2 * x - 1), h22])

          have h29 : (sqrt (x - sqrt (2 * x - 1))) ^ 2 = x - sqrt (2 * x - 1) := by
            exact Real.sq_sqrt (show 0 ≤ x - Real.sqrt (2 * x - 1) by linarith [Real.sqrt_nonneg (2 * x - 1), Real.sqrt_nonneg (2 * x - 1), h23])

          have h30 : Real.sqrt (x + Real.sqrt (2 * x - 1)) * Real.sqrt (x - Real.sqrt (2 * x - 1)) = Real.sqrt ((x + Real.sqrt (2 * x - 1)) * (x - Real.sqrt (2 * x - 1))) := by
            rw [← Real.sqrt_mul (by positivity)]

          have h31 : (x + Real.sqrt (2 * x - 1)) * (x - Real.sqrt (2 * x - 1)) = x ^ 2 - (Real.sqrt (2 * x - 1)) ^ 2 := by
            ring

          have h32 : Real.sqrt ((x + Real.sqrt (2 * x - 1)) * (x - Real.sqrt (2 * x - 1))) = Real.sqrt (x^2 - (Real.sqrt (2 * x - 1)) ^ 2) := by
            rw [h31]

          have h33 : (Real.sqrt (2 * x - 1)) ^ 2 = 2 * x - 1 := by
            exact Real.sq_sqrt (show 0 ≤ 2 * x - 1 by linarith)

          have h34 : Real.sqrt (x^2 - (Real.sqrt (2 * x - 1)) ^ 2) = abs (x - 1) := by
            rw [h33]
            have h35 : Real.sqrt (x^2 - (2 * x - 1)) = abs (x - 1) := by
              have h56 : x^2 - (2 * x - 1) = (x - 1)^2 := by ring
              rw [h56]
              have h57 : Real.sqrt ((x - 1) ^ 2) = abs (x - 1) := Real.sqrt_sq_eq_abs (x - 1)
              exact h57
            exact h35

          rw [h28, h29, h30, h32, h34]
          by_cases h35 : x - 1 ≥ 0
          · -- Case where x ≥ 1
            rw [abs_of_nonneg h35]
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

          · -- Case where x < 1
            rw [abs_of_neg (show x - 1 < 0 by linarith)]
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

        have h27 : (sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
        have h28 : (sqrt (x + sqrt (2 * x - 1)) + sqrt (x - sqrt (2 * x - 1))) ^ 2 = (sqrt 2) ^ 2 := by
          linarith [h25, h27]

        nlinarith [Real.sqrt_nonneg (x + sqrt (2 * x - 1)), Real.sqrt_nonneg (x - sqrt (2 * x - 1)), Real.sqrt_nonneg 2]

      exact h24