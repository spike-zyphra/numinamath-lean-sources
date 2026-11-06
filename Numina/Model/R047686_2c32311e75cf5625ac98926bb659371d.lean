import Mathlib

theorem algebra_222540 :
    {(x, y, z) : ℝ × ℝ × ℝ | 0 ≤ 7 * x - 3 ∧ 0 ≤ 7 * y - 3 ∧ 0 ≤ 7 * z - 3 ∧ 
    x ^ 2 + 7 * y + 2 = 2 * z + 4 * Real.sqrt (7 * x - 3) ∧ 
    y ^ 2 + 7 * z + 2 = 2 * x + 4 * Real.sqrt (7 * y - 3) ∧ 
    z ^ 2 + 7 * x + 2 = 2 * y + 4 * Real.sqrt (7 * z - 3)} = {(1, 1, 1)} := by

  ext ⟨x, y, z⟩
  simp [-Real.sqrt_nonneg]
  constructor
  · -- Assume h
    rintro ⟨h1, h2, h3, heq1, heq2, heq3⟩

    have h4 : (Real.sqrt (7 * x - 3)) ≥ 0 := by positivity
    have h5 : (Real.sqrt (7 * y - 3)) ≥ 0 := by positivity
    have h6 : (Real.sqrt (7 * z - 3)) ≥ 0 := by positivity

    have h7 : (Real.sqrt (7 * x - 3)) ^ 2 = 7 * x - 3 := by
      rw [Real.sq_sqrt]
      nlinarith

    have h8 : (Real.sqrt (7 * y - 3)) ^ 2 = 7 * y - 3 := by
      rw [Real.sq_sqrt]
      nlinarith

    have h9 : (Real.sqrt (7 * z - 3)) ^ 2 = 7 * z - 3 := by
      rw [Real.sq_sqrt]
      nlinarith

    have h10 : (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          sq_nonneg (Real.sqrt (7 * x - 3) - 2), sq_nonneg (Real.sqrt (7 * y - 3) - 2), sq_nonneg (Real.sqrt (7 * z - 3) - 2),
          Real.sqrt_nonneg (7 * x - 3), Real.sqrt_nonneg (7 * y - 3), Real.sqrt_nonneg (7 * z - 3),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

    have hx1 : (x - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
    have hy1 : (y - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
    have hz1 : (z - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
    have hx2 : x - 1 = 0 := by
      rw [sq_eq_zero_iff] at hx1
      linarith
    have hy2 : y - 1 = 0 := by
      rw [sq_eq_zero_iff] at hy1
      linarith
    have hz2 : z - 1 = 0 := by
      rw [sq_eq_zero_iff] at hz1
      linarith
    have hx3 : x = 1 := by
      linarith
    have hy3 : y = 1 := by
      linarith
    have hz3 : z = 1 := by
      linarith
    simp [hx3, hy3, hz3]
  · -- Show that $(1,1,1)$ is a solution.
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · -- Show $0 \le 7*1-3.$
      norm_num
    constructor
    · -- Show 0 ≤ 7 * 1 - 3 ∧
      norm_num
    constructor
    · -- Show 0 ≤ 7 * 1 - 3 ∧
      norm_num
    constructor
    · -- Show x^2 + 7 y + 2 = 2 * z + 4 * Real.sqrt (7 * x - 3) ∧
      have h1 : Real.sqrt (7 * (1 : ℝ) - 3) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h1]
      norm_num
    constructor
    · -- Show y ^ 2 + 7 * z + 2 = 2 * x + 4 * Real.sqrt (7 * y - 3) ∧
      have h1 : Real.sqrt (7 * (1 : ℝ) - 3) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h1]
      norm_num
    · -- Show z ^ 2 + 7 * x + 2 = 2 * y + 4 * Real.sqrt (7 * z - 3)
      have h1 : Real.sqrt (7 * (1 : ℝ) - 3) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h1]
      norm_num