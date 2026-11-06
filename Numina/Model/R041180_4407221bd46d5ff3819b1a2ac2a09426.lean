import Mathlib

theorem algebra_250689 (x : ℝ) :
    (Real.sqrt (x^2 + x + 6) + Real.sqrt (x^2 - x - 4)) / (Real.sqrt (x^2 + x + 6) - Real.sqrt (x^2 - x - 4)) = 5 ↔
    x = 5 ∨ x = -12 / 5 := by
  constructor
  · -- Forward direction: if the equation holds, then x is one of the two solutions.
    intro h
    have h1 : Real.sqrt (x ^ 2 + x + 6) - Real.sqrt (x ^ 2 - x - 4) ≠ 0 := by
      by_contra h2
      rw [h2] at h
      norm_num at h

    have h2 : Real.sqrt (x ^ 2 + x + 6) + Real.sqrt (x ^ 2 - x - 4) = 5 * (Real.sqrt (x ^ 2 + x + 6) - Real.sqrt (x ^ 2 - x - 4)) := by
      have h1' : Real.sqrt (x ^ 2 + x + 6) - Real.sqrt (x ^ 2 - x - 4) ≠ 0 := h1
      field_simp [h1'] at h ⊢
      linarith

    have h3 : Real.sqrt (x ^ 2 + x + 6) ≥ 0 := Real.sqrt_nonneg (x^2 + x + 6)
    have h4 : Real.sqrt (x ^ 2 - x - 4) ≥ 0 := Real.sqrt_nonneg (x^2 - x - 4)

    have h5 : (Real.sqrt (x ^ 2 + x + 6)) ^ 2 = x^2 + x + 6 := by
      exact Real.sq_sqrt (show (0 : ℝ) ≤ x^2 + x + 6 by nlinarith [sq_nonneg (x + 1 / 2)])

    have h6 : (Real.sqrt (x ^ 2 - x - 4)) ^ 2 = x^2 - x - 4 := by
      have h7 : 0 ≤ x^2 - x - 4 := by
        by_contra h
        push_neg at h
        have h8 : Real.sqrt (x^2 - x - 4) = 0 := by
          rw [Real.sqrt_eq_zero']
          nlinarith
          all_goals nlinarith
        rw [h8] at h2
        nlinarith [Real.sqrt_nonneg (x^2 + x + 6)]
      exact Real.sq_sqrt h7

    have h7 : 3 * Real.sqrt (x ^ 2 - x - 4) = 2 * Real.sqrt (x ^ 2 + x + 6) := by
      nlinarith

    have h8 : (3 * Real.sqrt (x ^ 2 - x - 4))^2 = (2 * Real.sqrt (x ^ 2 + x + 6)) ^ 2 := by
      rw [h7]

    have h9 : (3 * Real.sqrt (x ^ 2 - x - 4))^2 = 9 * (Real.sqrt (x ^ 2 - x - 4) ^ 2) := by
      ring

    have h10 : (2 * Real.sqrt (x ^ 2 + x + 6)) ^ 2 = 4 * (Real.sqrt (x ^ 2 + x + 6) ^ 2) := by
      ring

    rw [h9, h10] at h8
    rw [h5, h6] at h8

    have h11 : 5 * x^2 - 13 * x - 60 = 0 := by
      nlinarith

    have h12 : (5 * x + 12) * (x - 5) = 0 := by
      nlinarith

    cases' (mul_eq_zero.1 h12) with h13 h14
    · -- Case where $5x + 12 = 0$
      right
      linarith
    · -- Case where $x - 5 = 0$
      left
      linarith
  · -- Backward direction: both values of x satisfy the equation.
    rintro (h | h)
    · -- Case x = 5
      rw [h]
      have h1 : Real.sqrt ((5 : ℝ) ^ 2 + (5 : ℝ) + 6) = Real.sqrt (36 : ℝ) := by norm_num
      have h2 : Real.sqrt ((5 : ℝ) ^ 2 - (5 : ℝ) - 4) = Real.sqrt (16 : ℝ) := by norm_num
      rw [h1, h2]
      have h3 : Real.sqrt (36 : ℝ) = (6 : ℝ) := Real.sqrt_eq_cases.mpr (by norm_num)
      have h4 : Real.sqrt (16 : ℝ) = (4 : ℝ) := Real.sqrt_eq_cases.mpr (by norm_num)
      rw [h3, h4]
      norm_num
    · -- Case x = -12/5
      rw [h]
      have h1 : Real.sqrt ((-12 / 5 : ℝ) ^ 2 + (-12 / 5 : ℝ) + 6) = Real.sqrt (234 / 25 : ℝ) := by
        ring_nf
      have h2 : Real.sqrt ((-12 / 5 : ℝ) ^ 2 - (-12 / 5 : ℝ) - 4) = Real.sqrt (104 / 25 : ℝ) := by
        ring_nf
      rw [h1, h2]
      have h3 : Real.sqrt (234 / 25 : ℝ) = Real.sqrt 234 / 5 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      have h4 : Real.sqrt (104 / 25 : ℝ) = Real.sqrt 104 / 5 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h3, h4]
      have h5 : 0 < Real.sqrt 234 := by 
        positivity
      have h6 : 0 < Real.sqrt 104 := by 
        positivity
      have h7 : Real.sqrt 234 ^ 2 = 234 := Real.sq_sqrt (by norm_num)
      have h8 : Real.sqrt 104 ^ 2 = 104 := Real.sq_sqrt (by norm_num)
      field_simp [(show Real.sqrt 234 - Real.sqrt 104 ≠ 0 by
        nlinarith [Real.sqrt_nonneg 234, Real.sqrt_nonneg 104, h5, h6, h7, h8]
      )]
      <;> nlinarith [Real.sqrt_nonneg 234, Real.sqrt_nonneg 104, h5, h6, h7, h8, sq_nonneg (Real.sqrt 234 - 5 * Real.sqrt 104), sq_nonneg (Real.sqrt 234 - 3 * Real.sqrt 26), sq_nonneg (Real.sqrt 104 - 2 * Real.sqrt 26), h7, h8, sq_nonneg (Real.sqrt 234 ^ 2 - 234), sq_nonneg (Real.sqrt 104 ^ 2 - 104) ]