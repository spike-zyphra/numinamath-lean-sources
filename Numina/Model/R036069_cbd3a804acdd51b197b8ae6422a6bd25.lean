import Mathlib

theorem algebra_12205 :
  IsGreatest {k : ℝ | k > 0 ∧ ∃ x y, 0 < x ∧ 0 < y ∧ 3 = k^2 * (x^2 / y^2 + y^2 / x^2) + k * (x / y + y / x)} ((-1 + √7) / 2) := by
  constructor
  · -- Show that ((-1 + √7) / 2) is in the set
    constructor
    · -- Show that ((-1 + √7) / 2) > 0
      have h1 : √7 > 1 := by
        have h2 : (1 : ℝ) ^ 2 < (7 : ℝ) := by norm_num
        have h3 : (1 : ℝ) < √7 := by
          rw [Real.lt_sqrt] <;> norm_num
        linarith
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
    · -- Show existence of x,y
      use 1, 1
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Verify equation
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), sq_nonneg (Real.sqrt 7 - 1)]
  · -- Show that ((-1 + √7) / 2) is greatest in the set
    intro k ⟨hk, ⟨x, y, hx, hy, heq⟩⟩
    have h1 : 0 < x / y := by
      apply div_pos
      exact hx
      exact hy
    have h2 : 0 < y / x := by
      apply div_pos
      exact hy
      exact hx
    have h3 : x / y + y / x ≥ 2 := by
      have h4 : x / y + y / x - 2 ≥ 0 := by
        have h5 : x / y + y / x - 2 = (x - y) ^ 2 / (x * y) := by
          field_simp
          <;> nlinarith
        rw [h5]
        have h6 : (x - y) ^ 2 ≥ 0 := by
          exact sq_nonneg (x - y)
        have h7 : x * y > 0 := by
          apply mul_pos
          exact hx
          exact hy
        apply div_nonneg
        exact h6
        linarith
      linarith
    have h4 : x^2 / y^2 + y^2 / x^2 = (x / y + y / x) ^ 2 - 2 := by
      field_simp
      <;> nlinarith
    have h5 : k ≤ ((-1 + √7) / 2) := by
      nlinarith [sq_nonneg (k + 1), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y), sq_nonneg (x / y - y / x), sq_nonneg (k - ((-1 + √7) / 2)), Real.sqrt_nonneg 7, Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), sq_nonneg ((x / y + y / x) - 2), mul_pos hx hy, mul_pos hx hx, mul_pos hy hy, sq_nonneg (k), sq_nonneg (x / y * y / x - 1), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), sq_nonneg ((x / y + y / x) - 2)]
    linarith