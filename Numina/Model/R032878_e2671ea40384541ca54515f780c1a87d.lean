import Mathlib

theorem algebra_9353 {p : ℝ} (hp : p > 0) (h : (2 - p) ^ 2 = 4 * p * (p - 2)) :
    ∃ m : ℝ, m ≠ 0 ∧ ∃ k : ℝ, k ≠ 0 ∧ ∃ M N T : ℝ × ℝ,
      M.1 ^ 2 = 4 * M.2 ∧ N.1 ^ 2 = 4 * N.2 ∧
      M.1 ≠ N.1 ∧ T.1 ≠ M.1 ∧ T.1 ≠ N.1 ∧
      (M.1 - T.1) * (N.1 - T.1) < (M.2 - T.2) * (N.2 - T.2) := by
  have hp2 : p = 2 := by
    nlinarith [sq_nonneg (p - 2), sq_nonneg (p + 2 / 3)]
  use 1
  constructor
  · -- Show m ≠ 0
    norm_num
  use 1
  constructor
  · -- Show k ≠ 0
    norm_num
  use (0, 0)
  use (4, 4)
  use (1, 0)
  constructor
  · -- Check M.1^2 = 4 * M.2
    norm_num
  constructor
  · -- Check N.1^2 = 4 * N.2
    norm_num
  constructor
  · -- Check M.1 ≠ N.1
    norm_num
  constructor
  · -- Check T.1 ≠ M.1
    norm_num
  constructor
  · -- Check T.1 ≠ N.1
    norm_num
  · -- Check (M.1 - T.1) * (N.1 - T.1) < (M.2 - T.2) * (N.2 - T.2)
    norm_num