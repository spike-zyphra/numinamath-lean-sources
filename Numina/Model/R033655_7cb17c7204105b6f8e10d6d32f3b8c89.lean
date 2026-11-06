import Mathlib

theorem algebra_179635 (x : ℝ) (hx : x ^ 2 - 121 ≥ 0 ∧ x ^ 2 - 4 ≥ 0) :
    2 * Real.sqrt (x ^ 2 - 121) + 11 * Real.sqrt (x ^ 2 - 4) = 7 * Real.sqrt 3 * x ↔ x = 14 := by
  constructor
  · -- Assume the equation holds, prove x = 14
    intro h_eq
    have h1 : x ^ 2 - 121 ≥ 0 := hx.1
    have h2 : x ^ 2 - 4 ≥ 0 := hx.2
    have h3 : Real.sqrt (x ^ 2 - 121) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h4 : Real.sqrt (x ^ 2 - 4) ≥ 0 := by
      apply Real.sqrt_nonneg
    -- We have the given equation, now do squaring with both sides and steps to reach conclusion
    have h7 : (2 * Real.sqrt (x ^ 2 - 121) + 11 * Real.sqrt (x ^ 2 - 4)) ^ 2 = (7 * Real.sqrt 3 * x) ^ 2 := by
      have h7 : 2 * Real.sqrt (x ^ 2 - 121) + 11 * Real.sqrt (x ^ 2 - 4) = 7 * Real.sqrt 3 * x := h_eq
      rw [h7]
    -- Then substitute into the expressions by expanding and comparing so sides in different variables 
    have h8 : (2 * Real.sqrt (x ^ 2 - 121) + 11 * Real.sqrt (x ^ 2 - 4)) ^ 2 =
        4 * (Real.sqrt (x ^ 2 - 121) ^ 2) + 121 * (Real.sqrt (x ^ 2 - 4) ^ 2) + 44 * (Real.sqrt (x ^ 2 - 121) * Real.sqrt (x ^ 2 - 4)) := by
      ring_nf
    have h9 : (7 * Real.sqrt 3 * x) ^ 2 = 49 * (Real.sqrt 3) ^ 2 * x ^ 2 := by
      ring_nf
    have h10 : Real.sqrt (x ^ 2 - 121) ^ 2 = x ^ 2 - 121 := by
      rw [Real.sq_sqrt]
      linarith
    have h11 : Real.sqrt (x ^ 2 - 4) ^ 2 = x ^ 2 - 4 := by 
      rw [Real.sq_sqrt]
      linarith
    have h12 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    rw [h8] at h7
    rw [h10, h11] at h7
    rw [h9, h12] at h7
    -- After manipulations to comparing the expansions to resolve to squared variables for solving
    have h15 : (4 * (x ^ 2 - 121) * (x ^ 2 - 4)) = ((x ^ 2 + 44) ^ 2) := by
      nlinarith [ sq_nonneg (Real.sqrt (x ^ 2 - 121) - Real.sqrt (x ^ 2 - 4)), Real.sqrt_nonneg (x ^ 2 - 121), Real.sqrt_nonneg (x ^ 2 - 4) ]
    -- After solving, we find that the solution, represented here into squared law to equation, which solve quadratic (now has 4 * expression ^0 to 0
    have h16 : x ^ 2 = 196 := by
      nlinarith [ h15, Real.sqrt_nonneg (3) ]
    -- It solves to  x^2  =  196
    have h17 : x ^ 2 = 196 := h16
    -- After solving to this side derivative x = x = 14 as well, -14 roots which can't satisifies from step 2 h_eq given squaring can't create problem to solve roots empty [0] - next
    have h19 : x = 14 ∨ x = -14 := by
      have h20 : x ^ 2 - 196 = 0 := by
        nlinarith
      have h21 : (x - 14) * (x + 14) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h21) with h22 h23
      · -- x - 14 = 0
        left
        linarith
      · -- x + 14 = 0
        right
        linarith
    cases h19 with
    | inl h20 =>
      linarith
    | inr h21 =>
      -- But we need to check error on negatives from root perspective
      exfalso
      nlinarith [ Real.sqrt_nonneg (x ^ 2 - 121), Real.sqrt_nonneg (x ^ 2 - 4), Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num) ]
  -- The answer 14 is trivial the only root of length monotonic is x^2 - sqrt(x^0) split at 128 or larger seen as, split that from a surface angle, however the reciprocation roots of (x,-0) different [0 ~ greater] as discussed in monotonics
  · -- Assume x = 14, prove the equation
    intro h_eq
    rw [h_eq
    ]
    have h1 : Real.sqrt (14 ^ 2 - 121) = 5 * Real.sqrt 3 := by
      have h2 : (14 : ℝ) ^ 2 - 121 = 75 := by
        norm_num
      rw [h2
      ]
      have h3 : Real.sqrt (75 : ℝ) = 5 * Real.sqrt 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h3
      ]
    have h4 : Real.sqrt (14 ^ 2 - 4) = 8 * Real.sqrt 3 := by
      have h5 : (14 : ℝ) ^ 2 - 4 = 192 := by
        norm_num
      rw [h5
      ]
      have h6 : Real.sqrt (192 : ℝ) = 8 * Real.sqrt 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h6
      ]
    rw [h1, h4
    ]
    nlinarith [ Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num) ]