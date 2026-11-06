import Mathlib

theorem algebra_292247 :
    IsGreatest {x | ∃ a b c : ℝ, x = (a^2 - b * c) * (b^2 - c * a) * (c^2 - a * b) ∧ a^2 + b^2 + c^2 = 1} (1 / 8) := by
  constructor
  · -- Prove 1/8 is in the set by showing (sqrt 1/2)^2 - (-sqrt 1/2) * 0 = 1/2
    use Real.sqrt (1 / 2), -Real.sqrt (1 / 2), 0
    constructor
    · -- Compute (sqrt(1/2)^2 - (-sqrt(1/2)) * 0) * ((-sqrt(1/2))^2 - 0 * Real.sqrt (1 / 2)) * (0^2 - Real.sqrt (1 / 2) * (-Real.sqrt (1 / 2))
      have h1 : (Real.sqrt (1 / 2)) ^ 2 = 1 / 2 := by
        rw [Real.sq_sqrt]
        norm_num
      have h2 : (-Real.sqrt (1 / 2)) ^ 2 = 1 / 2 := by
        rw [show (-Real.sqrt (1 / 2)) ^ 2 = (Real.sqrt (1 / 2)) ^ 2 by ring]
        rw [Real.sq_sqrt]
        norm_num
      simp [h1, h2]
      <;> ring_nf <;> norm_num
    · -- Verify that the sum of squares is 1
      have h1 : (Real.sqrt (1 / 2)) ^ 2 = 1 / 2 := by
        rw [Real.sq_sqrt]
        norm_num
      have h2 : (-Real.sqrt (1 / 2)) ^ 2 = 1 / 2 := by
        rw [show (-Real.sqrt (1 / 2)) ^ 2 = (Real.sqrt (1 / 2)) ^ 2 by ring]
        rw [Real.sq_sqrt]
        norm_num
      nlinarith [h1, h2]
  · -- Prove that 1/8 is the greatest value in the set
    intro x hx
    rcases hx with ⟨a, b, c, h_eq, h_sum⟩
    nlinarith [sq_nonneg (a * b + b * c + c * a), sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a^2 - b * c - 1 / 2), sq_nonneg (b^2 - c * a - 1 / 2), sq_nonneg (c^2 - a * b - 1 / 2)
    ]