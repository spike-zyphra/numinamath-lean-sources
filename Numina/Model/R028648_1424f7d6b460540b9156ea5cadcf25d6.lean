import Mathlib

theorem algebra_223680 {x : ℝ} (hx : x^2 - Real.sqrt 6 * x + 1 = 0) (hx2 : x ≠ 0) :
    |x^4 - 1 / x^4| = 8 * Real.sqrt 3 := by
  have h1 : x + 1 / x = Real.sqrt 6 := by
    have h2 : x^2 + 1 = Real.sqrt 6 * x := by
      have h3 : x^2 - Real.sqrt 6 * x + 1 = 0 := hx
      nlinarith
    field_simp [hx2] at *
    nlinarith [h2, Real.sqrt_nonneg 6]
  
  have h2 : x^2 + 1 / x^2 = 4 := by
    have h7 : x^2 + 1 / x^2 = (x + 1 / x) ^ 2 - 2 := by
      field_simp [hx2]
      <;> ring
    rw [h7, h1]
    have h4 : (Real.sqrt 6 : ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    nlinarith [h4]
  
  have h9 : x^2 - 1 / x^2 = Real.sqrt 12 ∨ x^2 - 1 / x^2 = -Real.sqrt 12 := by
    have h5 : (x^2 - 1 / x^2) ^ 2 = 12 := by
      have h6 : (x^2 - 1 / x^2) ^ 2 = (x^2 + 1 / x^2) ^ 2 - 4 := by
        field_simp [hx2]
        <;> nlinarith
      rw [h6, h2]
      nlinarith
    have h9 : (x^2 - 1 / x^2) ^ 2 - 12 = 0 := by
      nlinarith
    have h9_factorization : (x^2 - 1 / x^2 - Real.sqrt 12) * (x^2 - 1 / x^2 + Real.sqrt 12) = 0 := by
      nlinarith [Real.sqrt_nonneg 12, Real.sq_sqrt (show (0 : ℝ) ≤ (12 : ℝ) by norm_num)]

    cases' (mul_eq_zero.1 h9_factorization) with h11 h12

    · -- Case where $x^2 - 1/x^2 - \sqrt{12} = 0$, so $x^2 - 1/x^2 = \sqrt{12}$
      left
      nlinarith
    · -- Case where $x^2 - 1/x^2 + \sqrt{12} = 0$, so $x^2 - 1/x^2 = -\sqrt{12}$
      right
      nlinarith
  
  have h4 : x^4 + 1 / x^4 = 14 := by
    have h4 : x^4 + 1 / x^4 = (x^2 + 1 / x^2) ^ 2 - 2 := by
      field_simp [hx2]
      <;> ring
    rw [h4, h2]
    all_goals nlinarith
    all_goals nlinarith
  
  cases h9 with
  | inl h11 =>
    have eq2 : x^4 - 1 / x^4 = (x^2 - 1 / x^2) * (x^2 + 1 / x^2) := by
      field_simp [hx2]
      <;> ring
    have h10 : x^4 - 1 / x^4 = 8 * Real.sqrt 3 := by
      rw [eq2, h11, h2]
      have h8 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      nlinarith [h8]
    rw [h10]
    all_goals norm_num [abs_of_nonneg, Real.sqrt_nonneg]
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
  
  | inr h11 =>
    have eq2 : x^4 - 1 / x^4 = (x^2 - 1 / x^2) * (x^2 + 1 / x^2) := by
      field_simp [hx2]
      <;> ring
    have h10 : x^4 - 1 / x^4 = -8 * Real.sqrt 3 := by
      rw [eq2, h11, h2]
      have h8 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      nlinarith [h8]
    rw [h10]
    all_goals norm_num [abs_of_nonpos, abs_of_nonneg, Real.sqrt_nonneg]
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]