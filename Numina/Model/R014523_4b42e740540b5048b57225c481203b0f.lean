import Mathlib

open Real

theorem algebra_314985 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) (M : ℝ) (hM : M = sqrt (3 * a + 1) + sqrt (3 * b + 1) + sqrt (3 * c + 1)) :
    ⌊M⌋ = 4 := by
  have h1 : 4 ≤ M := by
    have h2 : sqrt (3 * a + 1) ≥ 1 + a := by
      nlinarith [Real.sqrt_nonneg (3 * a + 1), Real.sq_sqrt (show 0 ≤ (3 * a + 1 : ℝ) by nlinarith),
        sq_nonneg (sqrt (3 * a + 1) - (1 + a)), sq_nonneg (a - 1 / 2)]
    have h3 : sqrt (3 * b + 1) ≥ 1 + b := by
      nlinarith [Real.sqrt_nonneg (3 * b + 1), Real.sq_sqrt (show 0 ≤ (3 * b + 1 : ℝ) by nlinarith),
        sq_nonneg (sqrt (3 * b + 1) - (1 + b)), sq_nonneg (b - 1 / 2)]
    have h4 : sqrt (3 * c + 1) ≥ 1 + c := by
      nlinarith [Real.sqrt_nonneg (3 * c + 1), Real.sq_sqrt (show 0 ≤ (3 * c + 1 : ℝ) by nlinarith),
        sq_nonneg (sqrt (3 * c + 1) - (1 + c)), sq_nonneg (c - 1 / 2)]
    have h5 : M ≥ 4 := by
      linarith [hM, h2, h3, h4, h]
    linarith
  have h2 : M < 5 := by
    have h3 : sqrt (3 * a + 1) ≤ (3 * a + 2) / 2 := by
      nlinarith [Real.sqrt_nonneg (3 * a + 1), Real.sq_sqrt (show 0 ≤ (3 * a + 1 : ℝ) by nlinarith),
        sq_nonneg (sqrt (3 * a + 1) - (3 * a + 2) / 2)]
    have h4 : sqrt (3 * b + 1) ≤ (3 * b + 2) / 2 := by
      nlinarith [Real.sqrt_nonneg (3 * b + 1), Real.sq_sqrt (show 0 ≤ (3 * b + 1 : ℝ) by nlinarith),
        sq_nonneg (sqrt (3 * b + 1) - (3 * b + 2) / 2)]
    have h5 : sqrt (3 * c + 1) ≤ (3 * c + 2) / 2 := by
      nlinarith [Real.sqrt_nonneg (3 * c + 1), Real.sq_sqrt (show 0 ≤ (3 * c + 1 : ℝ) by nlinarith),
        sq_nonneg (sqrt (3 * c + 1) - (3 * c + 2) / 2)]
    have h6 : M ≤ (9 / 2 : ℝ) := by
      linarith [hM, h3, h4, h5]
    linarith
  have h3 : ⌊M⌋ = 4 := by
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith [h1, h2]
  exact h3