import Mathlib

theorem algebra_315273 {A B : ℝ}
    (hA : A^3 = Real.sqrt 125) (hB : B^2 = Real.sqrt 25) :
    A + B = 2 * Real.sqrt 5 ∨ A + B = 0 := by

  have h1 : Real.sqrt 125 = 5 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num

  have h2 : Real.sqrt 25 = (5 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

  rw [h1] at hA
  rw [h2] at hB

  have hB1 : B = Real.sqrt 5 ∨ B = -Real.sqrt 5 := by
    have h1 : B^2 = (5 : ℝ) := by linarith
    have h4 : B = Real.sqrt 5 ∨ B = -Real.sqrt 5 := by
      have h5 : B^2 - (5 : ℝ) = 0 := by linarith
      have h6 : (B - Real.sqrt 5) * (B + Real.sqrt 5) = 0 := by
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      cases' (mul_eq_zero.mp h6) with h7 h8
      · -- case where $b - \sqrt{5} = 0$
        left
        linarith
      · -- case where $b + \sqrt{5} = 0$
        right
        nlinarith [Real.sqrt_nonneg 5]
    simpa using h4

  cases hB1 with
  | inl hB3 =>
    -- Case 1: B = sqrt 5
    -- Now solving for A
    have hA1 : A^3 = (5 * Real.sqrt 5 : ℝ) := hA

    have h7 : A = Real.sqrt 5 := by
      have h8 : A^3 = (5 * Real.sqrt 5 : ℝ) := hA1
      have h9 : (Real.sqrt 5 : ℝ) ^ 3 = (5 * Real.sqrt 5 : ℝ) := by
        calc
          (Real.sqrt 5 : ℝ) ^ 3 = (Real.sqrt 5) ^ 2 * Real.sqrt 5 := by ring
          _ = (5 : ℝ) * Real.sqrt 5 := by
            rw [Real.sq_sqrt]
            all_goals linarith
          _ = (5 * Real.sqrt 5 : ℝ) := by ring
      have h10 : A^3 = (Real.sqrt 5 : ℝ) ^ 3 := by
        linarith [h8, h9]
      -- because x^3 is strictly increasing, so it's injective
      have h11 : A = Real.sqrt 5 := by
        have h12 : A ^ 3 - (Real.sqrt 5) ^ 3 = 0 := by nlinarith
        have h13 : A ^ 3 - (Real.sqrt 5 : ℝ) ^ 3 = (A - Real.sqrt 5) * (A ^ 2 + A * Real.sqrt 5 + (Real.sqrt 5 : ℝ) ^ 2) := by ring
        rw [h13] at h12
        cases' (mul_eq_zero.mp h12) with h14 h15
        · -- case where $a - \sqrt{5} = 0$
          linarith
        · -- case where $a^2 + a \sqrt{5} + 5 = 0$
          nlinarith [sq_nonneg (A + Real.sqrt 5), sq_nonneg (A), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      assumption

    -- Now we can calculate $A + B$
    have hAB : A + B = 2 * Real.sqrt 5 := by
      rw [h7, hB3]
      all_goals nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

    left
    exact hAB

  | inr hB3 =>
    -- Case 2: B = -sqrt 5
    have hA1 : A^3 = (5 * Real.sqrt 5 : ℝ) := hA

    have h7 : A = Real.sqrt 5 := by
      have h8 : A^3 = (5 * Real.sqrt 5 : ℝ) := hA1
      have h9 : (Real.sqrt 5 : ℝ) ^ 3 = (5 * Real.sqrt 5 : ℝ) := by
        calc
          (Real.sqrt 5 : ℝ) ^ 3 = (Real.sqrt 5 : ℝ) ^ 2 * Real.sqrt 5 := by ring
          _ = (5 : ℝ) * Real.sqrt 5 := by
            rw [Real.sq_sqrt]
            all_goals linarith
          _ = (5 * Real.sqrt 5 : ℝ) := by ring
      have h10 : A^3 = (Real.sqrt 5 : ℝ) ^ 3 := by
        linarith [h8, h9]
      -- because x^3 is strictly increasing, so it's injective
      have h11 : A = Real.sqrt 5 := by
        have h12 : A ^ 3 - (Real.sqrt 5) ^ 3 = 0 := by nlinarith
        have h13 : A ^ 3 - (Real.sqrt 5 : ℝ) ^ 3 = (A - Real.sqrt 5) * (A ^ 2 + A * Real.sqrt 5 + (Real.sqrt 5 : ℝ) ^ 2) := by ring
        rw [h13] at h12
        cases' (mul_eq_zero.mp h12) with h14 h15
        · -- case where $a - \sqrt{5} = 0$
          linarith
        · -- case where $a^2 + a \sqrt{5} + 5 = 0$
          nlinarith [sq_nonneg (A + Real.sqrt 5), sq_nonneg (A), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      assumption

    -- Now we can calculate $A + B$
    have hAB1 : A + B = (0 : ℝ) := by
      rw [h7, hB3]
      all_goals nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

    right
    exact hAB1