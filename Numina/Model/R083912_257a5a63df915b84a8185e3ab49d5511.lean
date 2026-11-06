import Mathlib

theorem algebra_131123 (x : ℝ) :
    Real.sqrt (2 * x ^ 2 + x + 3) + Real.sqrt (x ^ 2 + x + 1) =
    Real.sqrt (5 * x ^ 2 + 3 * x + 7) ↔ x = -1 ∨ x = -1 / 2 := by
  constructor
  · -- Forward direction: equation implies solutions
    intro h
    have h1 : Real.sqrt (2 * x ^ 2 + x + 3) ≥ 0 := Real.sqrt_nonneg (2 * x^2 + x + 3)
    have h2 : Real.sqrt (x ^ 2 + x + 1) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + x + 1)
    have h3 : Real.sqrt (5 * x ^ 2 + 3 * x + 7) ≥ 0 := Real.sqrt_nonneg (5 * x^2 + 3 * x + 7)
    have h4 : (Real.sqrt (2 * x ^ 2 + x + 3) + Real.sqrt (x ^ 2 + x + 1)) ^ 2 = (Real.sqrt (5 * x ^ 2 + 3 * x + 7)) ^ 2 := by
      rw [h]
    have h5 : (Real.sqrt (2 * x ^ 2 + x + 3) + Real.sqrt (x ^ 2 + x + 1)) ^ 2 = (Real.sqrt (2 * x ^ 2 + x + 3)) ^ 2 + (Real.sqrt (x ^ 2 + x + 1)) ^ 2 + 2 * (Real.sqrt (2 * x ^ 2 + x + 3) * Real.sqrt (x ^ 2 + x + 1)) := by ring
    rw [h5] at h4
    have h6 : (Real.sqrt (2 * x ^ 2 + x + 3)) ^ 2 = 2 * x ^ 2 + x + 3 := by
      exact Real.sq_sqrt (by nlinarith)
    have h7 : (Real.sqrt (x ^ 2 + x + 1)) ^ 2 = x ^ 2 + x + 1 := by
      exact Real.sq_sqrt (by nlinarith)
    have h8 : (Real.sqrt (5 * x ^ 2 + 3 * x + 7)) ^ 2 = 5 * x ^ 2 + 3 * x + 7 := by
      exact Real.sq_sqrt (by nlinarith)
    rw [h6, h7, h8] at h4
    have h9 : 2 * Real.sqrt (2 * x ^ 2 + x + 3) * Real.sqrt (x ^ 2 + x + 1) = 2 * x ^ 2 + x + 3 := by
      nlinarith
    have h10 : Real.sqrt (2 * x ^ 2 + x + 3) * Real.sqrt (x ^ 2 + x + 1) = (2 * x ^ 2 + x + 3) / 2 := by
      linarith
    have h11 : (Real.sqrt (2 * x ^ 2 + x + 3) * Real.sqrt (x ^ 2 + x + 1)) ^ 2 = ((2 * x ^ 2 + x + 3) / 2) ^ 2 := by
      rw [h10]
    have h12 : (Real.sqrt (2 * x ^ 2 + x + 3) * Real.sqrt (x ^ 2 + x + 1)) ^ 2 = (Real.sqrt (2 * x ^ 2 + x + 3)) ^ 2 * (Real.sqrt (x ^ 2 + x + 1)) ^ 2 := by
      rw [mul_pow]
    rw [h12] at h11
    rw [h6, h7] at h11
    ring_nf at h11
    -- Solving the quartic equation 4x^4 + 8x^3 + 11x^2 + 10x + 3 = 0
    have h_eq : 4 * x ^ 4 + 8 * x ^ 3 + 11 * x ^ 2 + 10 * x + 3 = 0 := by nlinarith [h11]
    -- Factorization of the quartic equation
    have h_eq1 : (x + 1) * (x + 1/2) * (4 * x ^ 2 + 2 * x + 3) = 0 := by
      nlinarith [h_eq]
    cases' (mul_eq_zero.mp h_eq1) with h13 h14
    cases' (mul_eq_zero.mp h13) with h15 h16
    · left
      linarith
    · right
      linarith
    · have h17 : 4 * x ^ 2 + 2 * x + 3 > 0 := by
        nlinarith [sq_nonneg (2 * x + 0.5)]
      nlinarith
  · -- Reverse direction: solutions satisfy equation
    rintro (h | h)
    · -- x = -1
      rw [h]
      have h1 : Real.sqrt (2 * (-1) ^ 2 + (-1) + 3) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.sqrt ((-1) ^ 2 + (-1) + 1) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h3 : Real.sqrt (5 * (-1) ^ 2 + 3 * (-1) + 7) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1, h2, h3]
      all_goals norm_num
    · -- x = -1/2
      rw [h]
      have h4 : Real.sqrt (2 * (-1/2) ^ 2 + (-1/2) + 3) = Real.sqrt 3 := by
        ring_nf
      have h5 : Real.sqrt ((-1/2) ^ 2 + (-1/2) + 1) = Real.sqrt 3 / 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      have h6 : Real.sqrt (5 * (-1/2) ^ 2 + 3 * (-1/2) + 7) = (3 * Real.sqrt 3) / 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h4, h5, h6]
      ring_nf <;> norm_num
      <;> ring