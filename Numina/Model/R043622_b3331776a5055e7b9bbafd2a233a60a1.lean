import Mathlib
theorem algebra_605450 : IsGreatest {a : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 3 ∧ a = √x + √(2 * y + 2) + √(3 * z + 6)} 6:= by
  constructor
  · -- Let's prove that 6 is indeed in the set by choosing x = y = z = 1
    use 1, 1, 1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    have h1 : √(1 : ℝ) = 1 := by simp
    have h2 : √(2 * (1 : ℝ) + 2) = 2 := by
      rw [show (2 * (1 : ℝ) + 2 : ℝ) = 4 by norm_num]
      exact Real.sqrt_eq_cases.2 (by norm_num)
    have h3 : √(3 * (1 : ℝ) + 6) = 3 := by
      rw [show (3 * (1 : ℝ) + 6 : ℝ) = 9 by norm_num]
      exact Real.sqrt_eq_cases.2 (by norm_num)
    rw [h1, h2, h3]
    all_goals norm_num
  · -- Let's prove that 6 is greatest
    intro a ha
    rcases ha with ⟨x, y, z, hx, hy, hz, heq, ha⟩
    have h1 : √x + √(2 * y + 2) + √(3 * z + 6) ≤ 6 := by
      nlinarith [sq_nonneg (√x - 1), sq_nonneg (√(2 * y + 2) - 2), sq_nonneg (√(3 * z + 6) - 3),
        Real.sqrt_nonneg x, Real.sqrt_nonneg (2 * y + 2), Real.sqrt_nonneg (3 * z + 6),
        Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith),
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 * y + 2 : ℝ) by nlinarith),
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 * z + 6 : ℝ) by nlinarith),
        heq, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (2 * y + 2)),
        mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (3 * z + 6)),
        mul_nonneg (Real.sqrt_nonneg (2 * y + 2)) (Real.sqrt_nonneg (3 * z + 6))
      ]
    linarith [h1, ha]