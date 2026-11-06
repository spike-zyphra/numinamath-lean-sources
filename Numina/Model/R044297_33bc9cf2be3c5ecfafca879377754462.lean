import Mathlib

theorem algebra_186903 (x : ℝ) (hx : x ≠ 0) (h : x^2 - x ≥ 0) :
    1 / (x - Real.sqrt (x^2 - x)) - 1 / (x + Real.sqrt (x^2 - x)) = Real.sqrt 3 ↔ x = 4 := by
  constructor
  · -- Assume equation holds, prove x = 4
    intro heq
    have h1 : Real.sqrt (x^2 - x) ≥ 0 := Real.sqrt_nonneg (x^2 - x)
    have h2 : x - Real.sqrt (x^2 - x) ≠ 0 := by
      by_contra h2
      have h3 : Real.sqrt (x^2 - x) = x := by linarith
      have h4 : (Real.sqrt (x^2 - x)) ^ 2 = x ^ 2 - x := Real.sq_sqrt (show x^2 - x ≥ 0 by linarith)
      rw [h3] at h4
      have h5 : x ^ 2 - x = x ^ 2 := by nlinarith
      have h6 : -x = (0 : ℝ) := by linarith
      have h7 : x = (0 : ℝ) := by linarith
      contradiction
    have h3 : x + Real.sqrt (x^2 - x) ≠ 0 := by
      by_contra h3
      have h4 : Real.sqrt (x^2 - x) = -x := by
        linarith
      have h4' : Real.sqrt (x^2 - x) ≥ 0 := Real.sqrt_nonneg (x^2 - x)
      have h5 : -x ≥ 0 := by linarith [h4]
      have h6 : (Real.sqrt (x^2 - x)) ^ 2 = (-x) ^ 2 := by
        rw [h4]
      have h7 : (Real.sqrt (x^2 - x)) ^ 2 = x ^ 2 - x := Real.sq_sqrt (by linarith)
      have h8 : (-x : ℝ) ^ 2 = x ^ 2 := by
        nlinarith
      have h9 : x ^ 2 - x = x ^ 2 := by
        nlinarith
      have h10 : -x = (0 : ℝ) := by linarith
      have h11 : x = (0 : ℝ) := by linarith
      contradiction
    have eq1 : 1 / (x - Real.sqrt (x^2 - x)) - 1 / (x + Real.sqrt (x^2 - x)) =
      2 * Real.sqrt (x^2 - x) / x := by
      have h4 : (x - Real.sqrt (x^2 - x)) * (x + Real.sqrt (x^2 - x)) = x := by
        nlinarith [Real.sqrt_nonneg (x ^ 2 - x), Real.sq_sqrt (show x ^ 2 - x ≥ 0 by linarith)]
      field_simp [(show x - Real.sqrt (x^2 - x) ≠ 0 by exact h2), (show x + Real.sqrt (x^2 - x) ≠ 0 by exact h3), show x ≠ 0 by exact hx]
      <;> nlinarith [Real.sqrt_nonneg (x ^ 2 - x), Real.sq_sqrt (show x ^ 2 - x ≥ 0 by linarith)]
    have eq2 : 2 * Real.sqrt (x^2 - x) / x = Real.sqrt 3 := by
      rw [eq1] at heq
      linarith
    have eq3 : 2 * Real.sqrt (x^2 - x) = x * Real.sqrt 3 := by
      have h4 : x ≠ 0 := hx
      field_simp at eq2 ⊢
      <;> nlinarith
    have eq4 : (2 * Real.sqrt (x^2 - x)) ^ 2 = (x * Real.sqrt 3) ^ 2 := by
      rw [eq3]
    have eq5 : (2 * Real.sqrt (x^2 - x)) ^ 2 = 4 * (x ^ 2 - x) := by
      calc
        (2 * Real.sqrt (x^2 - x)) ^ 2
          = 4 * (Real.sqrt (x ^ 2 - x) ^ 2) := by ring_nf
        _ = 4 * (x ^ 2 - x) := by
          rw [Real.sq_sqrt (by linarith)]
    have eq6 : (x * Real.sqrt 3) ^ 2 = 3 * x ^ 2 := by
      calc
        (x * Real.sqrt 3) ^ 2
          = x ^ 2 * (Real.sqrt 3) ^ 2 := by ring_nf
        _ = x ^ 2 * 3 := by
          rw [Real.sq_sqrt (by norm_num)]
        _ = 3 * x ^ 2 := by ring_nf
    have eq7 : 4 * (x ^ 2 - x) = 3 * x ^ 2 := by
      nlinarith [eq4, eq5, eq6]
    have eq8 : x ^ 2 - 4 * x = 0 := by
      nlinarith
    have eq9 : x * (x - 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 eq9) with h10 h11
    · -- Case x = 0, which is a contradiction
      exfalso
      apply hx
      linarith
    · -- Case x - 4 = 0, so x = 4
      linarith
  · -- Assume x = 4, prove equation
    intro heq
    rw [heq]
    have h42 : Real.sqrt ((4 : ℝ) ^ 2 - (4 : ℝ)) = (2 : ℝ) * (Real.sqrt 3) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h42]
    have h5 : 1 / ((4 : ℝ) - (2 : ℝ) * Real.sqrt 3) - 1 / ((4 : ℝ) + (2 : ℝ) * Real.sqrt 3) = Real.sqrt 3 := by
      have h6 : ((4 : ℝ) - (2 : ℝ) * Real.sqrt 3) ≠ 0 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h7 : ((4 : ℝ) + (2 : ℝ) * Real.sqrt 3) ≠ 0 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      field_simp [h6, h7, Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      <;> nlinarith [Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 - 2), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3), sq_nonneg (Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg ((4: ℝ) - (2: ℝ) * Real.sqrt 3), sq_nonneg ((4: ℝ) + (2: ℝ) * Real.sqrt 3), Real.sqrt_nonneg 3]
    linarith [h5]