import Mathlib

theorem algebra_296777 (x : ℝ) (hx : x^2 + Real.sqrt 3 * x + 7 / 4 ≥ 0 ∧ x^2 - 3 * Real.sqrt 3 * x + 31 / 4 ≥ 0) :
    Real.sqrt (x^2 + Real.sqrt 3 * x + 7 / 4) + Real.sqrt (x^2 - 3 * Real.sqrt 3 * x + 31 / 4) = 4 ↔
    x = Real.sqrt 3 / 2 := by
  constructor
  · intro h
    rcases hx with ⟨hx1, hx2⟩
    have h1 : Real.sqrt (x^2 + Real.sqrt 3 * x + 7 / 4) = Real.sqrt ((x + Real.sqrt 3 / 2) ^ 2 + 1) := by
      have h2 : (x^2 + Real.sqrt 3 * x + 7 / 4 : ℝ) = (x + Real.sqrt 3 / 2) ^ 2 + 1 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      rw [h2]
    have h11 : Real.sqrt (x^2 + Real.sqrt 3 * x + 7 / 4) ≥ 0 := by positivity
    have h2 : Real.sqrt (x^2 - 3 * Real.sqrt 3 * x + 31 / 4) = Real.sqrt ((x - 3 * Real.sqrt 3 / 2) ^ 2 + 1) := by
      have h3 : (x^2 - 3 * Real.sqrt 3 * x + 31 / 4 : ℝ) = (x - 3 * Real.sqrt 3 / 2) ^ 2 + 1 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      rw [h3]
    have h22 : Real.sqrt (x^2 - 3 * Real.sqrt 3 * x + 31 / 4) ≥ 0 := by positivity
    rw [h1, h2] at h
    have h3 : Real.sqrt ((x + Real.sqrt 3 / 2) ^ 2 + 1) ≥ 0 := by positivity
    have h4 : Real.sqrt ((x - 3 * Real.sqrt 3 / 2) ^ 2 + 1) ≥ 0 := by positivity
    have h33 : Real.sqrt ((x + Real.sqrt 3 / 2) ^ 2 + 1) ^ 2 = (x + Real.sqrt 3 / 2) ^ 2 + 1 := by
      rw [Real.sq_sqrt]
      positivity
    have h44 : Real.sqrt ((x - 3 * Real.sqrt 3 / 2) ^ 2 + 1) ^ 2 = (x - 3 * Real.sqrt 3 / 2) ^ 2 + 1 := by
      rw [Real.sq_sqrt]
      positivity
    have h34 : Real.sqrt ((x + Real.sqrt 3 / 2) ^ 2 + 1) + Real.sqrt ((x - 3 * Real.sqrt 3 / 2) ^ 2 + 1) = 4 := by
      linarith
    have h34' : (Real.sqrt ((x + Real.sqrt 3 / 2) ^ 2 + 1) + Real.sqrt ((x - 3 * Real.sqrt 3 / 2) ^ 2 + 1) ) ^ 2 = 16 := by
      rw [h34]
      norm_num
    have eq1 : (Real.sqrt ((x + Real.sqrt 3 / 2) ^ 2 + 1) ) ^ 2 + (Real.sqrt ((x - 3 * Real.sqrt 3 / 2) ^ 2 + 1) ) ^ 2 + 2 * (Real.sqrt ((x + Real.sqrt 3 / 2) ^ 2 + 1) * Real.sqrt ((x - 3 * Real.sqrt 3 / 2) ^ 2 + 1) ) = 16 := by 
      linarith [h34']
    rw [h33, h44] at eq1
    have eq2 : (x - Real.sqrt 3 / 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - Real.sqrt 3 / 2), sq_nonneg (2 * x * (Real.sqrt 3)), sq_nonneg (x * (Real.sqrt 3) / 2), sq_nonneg ((x + Real.sqrt 3 / 2) ), sq_nonneg ((x - 3 * Real.sqrt 3 / 2) ), sq_nonneg (Real.sqrt ((x + Real.sqrt 3 / 2) ^ 2 + 1) * Real.sqrt ((x - 3 * Real.sqrt 3 / 2) ^ 2 + 1)), Real.sqrt_nonneg ((x + Real.sqrt 3 / 2) ^ 2 + 1), Real.sqrt_nonneg ((x - 3 * Real.sqrt 3 / 2) ^ 2 + 1), Real.sqrt_nonneg 3, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3), mul_nonneg (Real.sqrt_nonneg ((x + Real.sqrt 3 / 2) ^ 2 + 1)) (Real.sqrt_nonneg ((x - 3 * Real.sqrt 3 / 2) ^ 2 + 1)), Real.mul_self_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg ((x + Real.sqrt 3 / 2) ^ 2 + 1), Real.sqrt_nonneg ((x - 3 * Real.sqrt 3 / 2) ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have eq3 : x - Real.sqrt 3 / 2 = 0 := by
      nlinarith
    linarith
  · -- Backward direction: if x = sqrt(3)/2, then the equation holds
    intro h
    rw [h]
    have h1 : Real.sqrt ((Real.sqrt 3 / 2 : ℝ) ^ 2 + Real.sqrt 3 * (Real.sqrt 3 / 2) + 7 / 4) = 2 := by
      have h11 : (Real.sqrt 3 / 2 : ℝ) ^ 2 + Real.sqrt 3 * (Real.sqrt 3 / 2) + 7 / 4 = 4 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      rw [h11]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    have h2 : Real.sqrt ((Real.sqrt 3 / 2 : ℝ) ^ 2 - 3 * Real.sqrt 3 * (Real.sqrt 3 / 2) + 31 / 4) = 2 := by
      have h11 : (Real.sqrt 3 / 2 : ℝ) ^ 2 - 3 * Real.sqrt 3 * (Real.sqrt 3 / 2) + 31 / 4 = 4 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      rw [h11]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    rw [h1, h2]
    <;> linarith
    all_goals
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]