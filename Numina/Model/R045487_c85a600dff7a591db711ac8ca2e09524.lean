import Mathlib

theorem algebra_610497 :
    IsGreatest {z | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ x + 1 / y = 3 ∧ y + 2 / x = 3 ∧ z = x * y} (3 + Real.sqrt 7) := by
  constructor
  · -- Show 3 + Real.sqrt 7 is in the set
    use (5 + Real.sqrt 7) / 3, (4 + Real.sqrt 7) / 3
    constructor
    · -- Show x > 0
      have h1 : 0 < Real.sqrt 7 := by
        positivity
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
    constructor
    · -- Show y > 0
      have h1 : 0 < Real.sqrt 7 := by
        positivity
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
    constructor
    · -- Show x + 1 / y = 3
      field_simp [(show (4 + Real.sqrt 7: ℝ) ≠ 0 by
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
      )]
      <;> nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), mul_nonneg (Real.sqrt_nonneg 7) (Real.sqrt_nonneg 7)]
    constructor
    · -- Show y + 2 / x = 3
      field_simp [(show (5 + Real.sqrt 7: ℝ) ≠ 0 by
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
      )]
      <;> nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), mul_nonneg (Real.sqrt_nonneg 7) (Real.sqrt_nonneg 7)]
    · -- Show z = x * y
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
  · -- Show 3 + Real.sqrt 7 is greatest in the set
    intro z hz
    rcases hz with ⟨x, y, hx, hy, h1, h2, hz⟩
    have eq1 : x * y = 3 * y - 1 := by 
      have h1' : y ≠ 0 := by linarith
      field_simp at h1 ⊢
      linarith
    have eq2 : x * y = 3 * x - 2 := by
      have h2' : x ≠ 0 := by linarith
      field_simp at h2 ⊢
      linarith
    have eq3 : 3 * y - 1 = 3 * x - 2 := by
      linarith [eq1, eq2]
    have eq4 : y = x - 1 / 3 := by 
      linarith
    have eq5 : 3 * x ^ 2 - 10 * x + 6 = 0 := by
      have h2' : x ≠ 0 := by linarith
      have eq6 : (x - 1 / 3) * x + 2 = 3 * x := by
        rw [eq4] at h2
        field_simp at h2 ⊢
        nlinarith
      nlinarith
    have eq6 : x * y ≤ 3 + Real.sqrt 7 := by
      rw [eq4]
      nlinarith [sq_nonneg (x - (5 + Real.sqrt 7) / 3), sq_nonneg (x - (5 - Real.sqrt 7) / 3),
        Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), mul_nonneg (Real.sqrt_nonneg 7) (Real.sqrt_nonneg 7)]
    linarith [eq6, hz]