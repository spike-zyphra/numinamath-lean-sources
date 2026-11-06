import Mathlib

theorem algebra_605541 : {(a, b, c) : ℝ × ℝ × ℝ | a > 0 ∧ b > 0 ∧ c > 0 ∧
a * √b - c = a ∧ b * √c - a = b ∧ c * √a - b = c} = {(4, 4, 4)} := by
  ext ⟨a, b, c⟩
  simp
  constructor
  · -- First, prove that if (a, b, c) satisfies the system, then (a, b, c) = (4, 4, 4)
    rintro ⟨ha, hb, hc, h1, h2, h3⟩
    have h4 : a * √b = a + c := by linarith
    have h5 : b * √c = a + b := by linarith
    have h6 : c * √a = b + c := by linarith
    have h7 : √b ≥ 0 := by positivity
    have h8 : √c ≥ 0 := by positivity
    have h9 : √a ≥ 0 := by positivity
    have h10 : a = 4 := by
      nlinarith [sq_nonneg (√b - 2), sq_nonneg (√c - 2), sq_nonneg (√a - 2),
        Real.sqrt_nonneg b, Real.sqrt_nonneg c, Real.sqrt_nonneg a,
        Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ c by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith),
        mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c), mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg a), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
    have h11 : b = 4 := by
      nlinarith [sq_nonneg (√b - 2), sq_nonneg (√c - 2), sq_nonneg (√a - 2),
        Real.sqrt_nonneg b, Real.sqrt_nonneg c, Real.sqrt_nonneg a,
        Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ c by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith),
        mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c), mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg a), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
    have h12 : c = 4 := by
      nlinarith [sq_nonneg (√b - 2), sq_nonneg (√c - 2), sq_nonneg (√a - 2),
        Real.sqrt_nonneg b, Real.sqrt_nonneg c, Real.sqrt_nonneg a,
        Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ c by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith),
        mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c), mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg a), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
    simp [h10, h11, h12]
  · -- Verify that (4, 4, 4) is indeed a solution
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- First equation
      have h1 : (4 : ℝ) * √(4 : ℝ) - (4 : ℝ) = (4 : ℝ) := by
        have h8 : √(4 : ℝ) = 2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h8]
        all_goals norm_num
      linarith
    constructor
    · -- Second equation
      have h2 : (4 : ℝ) * √(4 : ℝ) - (4 : ℝ) = (4 : ℝ) := by
        have h8 : √(4 : ℝ) = 2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h8]
        all_goals norm_num
      linarith
    · -- Third equation
      have h3 : (4 : ℝ) * √(4 : ℝ) - (4 : ℝ) = (4 : ℝ) := by
        have h8 : √(4 : ℝ) = 2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h8]
        all_goals norm_num
      linarith