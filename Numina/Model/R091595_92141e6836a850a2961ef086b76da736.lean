import Mathlib

theorem algebra_19381 (h : Set (ℝ × ℝ)) (h_def : h = {(x, y) | x ^ 2 + y ^ 2 = 4 * x + 8 * y}) :
    IsLeast {d | ∃ x y, d = Real.sqrt ((x - 5) ^ 2 + (y + 2) ^ 2) ∧ (x, y) ∈ h} (Real.sqrt 5) := by
  constructor
  · -- Show sqrt(5) is in the set
    use 4, 0
    constructor
    · -- Show sqrt(5) = sqrt((4 - 5)^2 + (0 + 2)^2)
      have h1 : Real.sqrt ((4 - 5 : ℝ)^2 + (0 + 2)^2) = Real.sqrt 5 := by norm_num
      rw [h1]
      all_goals norm_num
    · -- Show (4, 0) ∈ h
      rw [h_def]
      all_goals norm_num
  · -- Show sqrt(5) is the smallest
    intro d hd
    rcases hd with ⟨x, y, df_eq, hxy⟩
    rw [h_def] at hxy
    simp at hxy
    have h_eq : Real.sqrt ((x - 5) ^ 2 + (y + 2) ^ 2) ≥ Real.sqrt 5 := by
      have h1 : (x - 5) ^ 2 + (y + 2) ^ 2 ≥ 5 := by
        nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 0), sq_nonneg (x + 1), sq_nonneg (y - 4)]
      have h2 : (x - 5) ^ 2 + (y + 2) ^ 2 ≥ (5 : ℝ) := by linarith
      exact Real.sqrt_le_sqrt (show (5 : ℝ) ≤ (x - 5) ^ 2 + (y + 2) ^ 2 by linarith)
    have h_le : d ≥ Real.sqrt 5 := by
      rw [df_eq] at *
      linarith
    linarith