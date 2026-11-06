import Mathlib

theorem algebra_129615 {a : ℝ} (ha : a ≠ 0) :
    ∃ x y : ℤ, x^2 - (a + 1 / a) * x + (a + 4 * Real.sqrt 5) * (1 / a - 4 * Real.sqrt 5) = 0 ∧
    y^2 - (a + 1 / a) * y + (a + 4 * Real.sqrt 5) * (1 / a - 4 * Real.sqrt 5) = 0 ↔
    a = 9 - 4 * Real.sqrt 5 := by
  use 9
  use 9
  constructor
  · -- Forward: if (9,9) are roots, then a = 9 - 4*sqrt(5)
    intro h
    rcases h with ⟨h1, h2⟩
    have eq1 : (9 : ℝ)^2 - (a + 1 / a) * (9 : ℝ) + (a + 4 * Real.sqrt 5) * (1 / a - 4 * Real.sqrt 5) = 0 := by
      norm_num at h1 ⊢
      linarith [h1]
    have eq2 : (a - (9 - 4 * Real.sqrt 5)) ^ 2 = 0 := by
      field_simp [ha] at eq1 ⊢
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (a - (9 - 4 * Real.sqrt 5)), sq_nonneg (a * Real.sqrt 5 - 4 * Real.sqrt 5 * 4 * Real.sqrt 5), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have eq3 : a - (9 - 4 * Real.sqrt 5) = 0 := by
      nlinarith [eq2]
    linarith [eq3]
  · -- Backward: if a = 9 - 4*sqrt(5), then (9,9) are roots
    intro h
    rw [h]
    constructor
    · -- First equation with a = 9 - 4*sqrt(5)
      norm_num
      <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 ^ 2)]
    · -- Second equation with a = 9 - 4*sqrt(5)
      norm_num
      <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 ^ 2)]