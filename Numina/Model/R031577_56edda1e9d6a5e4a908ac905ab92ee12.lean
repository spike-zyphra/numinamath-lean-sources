import Mathlib

open Real Set

theorem inequalities_157500 :
    IsGreatest {x | ∃ a b : ℝ, a ∈ Icc 0 1 ∧ b ∈ Icc 0 1 ∧ x = a * sqrt (1 - b) + b * sqrt (1 - a)} 1 := by
  constructor
  · -- First part: showing 1 is in the set
    use 1, 0
    constructor
    · -- Show 1 is in Icc 0 1
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 0 is in Icc 0 1
      exact ⟨by norm_num, by norm_num⟩
    · -- Show 1 = 1 * sqrt (1 - 0) + 0 * sqrt (1 - 1)
      have h1 : sqrt (1 - (0 : ℝ)) = 1 := by
        rw [Real.sqrt_eq_cases]
        norm_num
      have h2 : sqrt (1 - (1 : ℝ)) = 0 := by
        rw [show 1 - (1 : ℝ) = (0 : ℝ) by norm_num]
        simp
      rw [h1, h2]
      all_goals norm_num
  · -- Second part: showing it's a greatest
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hx⟩
    rcases ha with ⟨ha0, ha1⟩
    rcases hb with ⟨hb0, hb1⟩
    have h5 : sqrt (1 - b) ≤ 1 := by
      have h6 : 1 - b ≥ 0 := by linarith [hb1]
      have h7 : sqrt (1 - b) ≤ sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h8 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      linarith
    have h8 : sqrt (1 - a) ≤ 1 := by
      have h9 : 1 - a ≥ 0 := by linarith [ha1]
      have h10 : sqrt (1 - a) ≤ sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h11 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      linarith
    have h10 : a * sqrt (1 - b) + b * sqrt (1 - a) ≤ 1 := by
      nlinarith [sq_nonneg (sqrt (1 - b) - 1), sq_nonneg (sqrt (1 - a) - 1),
        Real.sqrt_nonneg (1 - b), Real.sqrt_nonneg (1 - a),
        h5, h8,
        mul_nonneg (show 0 ≤ (1 - a : ℝ) by linarith) (show 0 ≤ (1 - b : ℝ) by linarith),
        Real.sq_sqrt (show 0 ≤ (1 - b : ℝ) by linarith),
        Real.sq_sqrt (show 0 ≤ (1 - a : ℝ) by linarith),
        mul_nonneg (show 0 ≤ (a : ℝ) by linarith) (show 0 ≤ (b : ℝ) by linarith)
      ]
    linarith [hx, h10]