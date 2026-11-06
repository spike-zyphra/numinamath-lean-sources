import Mathlib

theorem algebra_297157 {m : ℝ} (hm : m ≠ 0) :
    ∃ x y, x ≠ 0 ∧ y ≠ 0 ∧ y = m * x ^ 1 - m ∧ x * y = 1 ↔ m = 2 := by 
  by_cases h1 : m = 2
  · -- Assume m = 2, prove the existence of x, y such that the conditions hold iff m = 2
    use (1 + Real.sqrt 3) / 2
    use Real.sqrt 3 - 1
    constructor
    · -- Forward implication: if conditions hold, then m = 2
      intro h
      rcases h with ⟨hx, hy, heq, hprod⟩
      tauto
    · -- Backward implication: if m = 2, then conditions hold
      intro heq
      have h_eq : m = 2 := by 
        tauto
      constructor
      · -- Show x ≠ 0
        have h2 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
        linarith
      constructor
      · -- Show y ≠ 0
        have h2 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      constructor
      · -- Show y = m * x ^ 1 - m
        rw [h_eq]
        field_simp
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      · -- Show x * y = 1
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  · -- Assume m ≠ 2
    use 0
    use 0
    simp [show m ≠ 2 by tauto]