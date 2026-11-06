import Mathlib

theorem algebra_10383 (x : ℝ) (hx : 2*x^2+x+3≥0 ∧ x^2+x+1≥0 ∧ 5*x^2+3*x+7≥0) :
    Real.sqrt (2*x^2+x+3) + Real.sqrt (x^2+x+1) = Real.sqrt (5*x^2+3*x+7) ↔
    x = -1 ∨ x = -1/2 := by

  have h1 : 2 * x ^ 2 + x + 3 ≥ 0 := hx.1
  have h2 : x ^ 2 + x + 1 ≥ 0 := hx.2.1
  have h3 : 5 * x ^ 2 + 3 * x + 7 ≥ 0 := hx.2.2

  constructor
  · -- Forward direction: equation → { -1, -1/2 }
    intro h_eq

    have h_eq1 : (Real.sqrt (2*x^2+x+3) + Real.sqrt (x^2+x+1)) ^ 2 = (Real.sqrt (5*x^2+3*x+7)) ^ 2 := by 
      rw [h_eq]

    have eq1 : (Real.sqrt (2 * x ^ 2 + x + 3) + Real.sqrt (x ^ 2 + x + 1)) ^ 2 =
        (Real.sqrt (2 * x^2 + x + 3)) ^ 2 + (Real.sqrt (x ^ 2 + x + 1)) ^ 2 + 2 * (Real.sqrt (2 * x^2 + x + 3) * Real.sqrt (x ^ 2 + x + 1)) := by
      ring

    have eq2 : (Real.sqrt (5 * x ^ 2 + 3 * x + 7)) ^ 2 = 5 * x ^ 2 + 3 * x + 7 := by
      apply Real.sq_sqrt
      linarith

    have eq3 : (Real.sqrt (2 * x^2 + x + 3)) ^ 2 = 2 * x^2 + x + 3 := by
      apply Real.sq_sqrt
      linarith
    have eq4 : (Real.sqrt (x ^ 2 + x + 1)) ^ 2 = x ^ 2 + x + 1 := by
      apply Real.sq_sqrt
      linarith

    rw [eq1, eq2, eq3, eq4] at h_eq1
    have eq5 : 2 * (Real.sqrt (2 * x^2 + x + 3) * Real.sqrt (x ^ 2 + x + 1)) = 2 * x^2 + x + 3 := by
      nlinarith

    have eq6 : (Real.sqrt (2 * x^2 + x + 3) * Real.sqrt (x ^ 2 + x + 1)) ^ 2 = (2 * x^2 + x + 3) * (x ^ 2 + x + 1) := by
      calc
        (Real.sqrt (2 * x^2 + x + 3) * Real.sqrt (x ^ 2 + x + 1)) ^ 2 = (Real.sqrt (2 * x^2 + x + 3) ) ^ 2 * (Real.sqrt (x ^ 2 + x + 1) ) ^ 2 := by 
          ring
        _ = (2 * x^2 + x + 3) * (x ^ 2 + x + 1) := by 
          rw [eq3, eq4]

    have h5 : (x + 1)^2 * (x + 1 / 2)^2 = 0 := by 
      nlinarith [sq_nonneg (Real.sqrt (2 * x^2 + x + 3) * Real.sqrt (x ^ 2 + x + 1) - (x^2 + x / 2 + 3 / 2)), sq_nonneg (Real.sqrt (2 * x^2 + x + 3) - Real.sqrt (x ^ 2 + x + 1)), Real.sqrt_nonneg (2 * x^2 + x + 3), Real.sqrt_nonneg (x ^ 2 + x + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x^2 + x + 3: ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (x^2 + x + 1: ℝ) by linarith), sq_nonneg (x+1), sq_nonneg (x+1/2)]

    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case where (x + 1)^2 = 0
      have : x + 1 = 0 := by
        apply pow_eq_zero 
        exact h6
      left
      linarith 
    · -- Case where (x + 1/2)^2 = 0
      have : x + 1 / 2 = 0 := by
        apply pow_eq_zero 
        exact h7
      right
      linarith

  · -- Backward direction: { -1, -1/2 } satisfy the equation.
    rintro (h | h)
    · -- Case x = -1
      rw [h]
      have h_eq1 : Real.sqrt (2 * (-1: ℝ) ^ 2 + (-1) + 3) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h_eq2 : Real.sqrt ((-1: ℝ) ^ 2 + (-1) + 1) = (1 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h_eq3 : Real.sqrt (5 * (-1: ℝ) ^ 2 + 3 * (-1) + 7) = (3 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h_eq1, h_eq2, h_eq3]
      all_goals norm_num
    · -- Case x = -1/2
      rw [h]
      have h_eq1 : Real.sqrt (2 * (-1 / 2: ℝ) ^ 2 + (-1 / 2) + 3) = Real.sqrt (3: ℝ) := by
        norm_num
      have h_eq2 : Real.sqrt ((-1 / 2: ℝ) ^ 2 + (-1 / 2) + 1) = Real.sqrt (3 / 4: ℝ) := by
        norm_num
      have h_eq3 : Real.sqrt (5 * (-1 / 2: ℝ) ^ 2 + 3 * (-1 / 2) + 7) = Real.sqrt (27 / 4: ℝ) := by
        norm_num
      rw [h_eq1, h_eq2, h_eq3]
      have h14 : Real.sqrt (3: ℝ) + Real.sqrt (3 / 4: ℝ) = Real.sqrt (27 / 4: ℝ) := by
        have h15 : Real.sqrt (3 / 4: ℝ) = Real.sqrt 3 / 2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf <;> norm_num
        have h16 : Real.sqrt (27 / 4: ℝ) = (3 * Real.sqrt 3) / 2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf <;> norm_num
        rw [h15, h16]
        linarith [Real.sqrt_nonneg (3: ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3: ℝ) by norm_num)]
      linarith [h14]