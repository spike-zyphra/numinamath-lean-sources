import Mathlib

open Real

theorem algebra_157324 :
    {x : ℝ | x ≥ 2 ∧ x < 3 ∧ logb 3 (3 - x) = sqrt (sqrt (x - 1) - 1 / sqrt (x - 1))} = {2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, prove that if x in left side, then x = 2
    rintro ⟨hx1, hx2, heq⟩
    have h4 : sqrt (x - 1) > 0 := by
      apply Real.sqrt_pos.2
      linarith
    have h5 : sqrt (sqrt (x - 1) - 1 / sqrt (x - 1)) ≥ 0 := by positivity
    have h6 : logb 3 (3 - x) ≥ 0 := by linarith
    have h7 : 3 - x > 0 := by linarith
    have h9 : (3 - x) ≥ 1 := by
      by_contra h
      push_neg at h
      have h10 : logb 3 (3 - x) < 0 := by
        have h11 : (3 - x) < 1 := by linarith
        have h12 : logb 3 (3 - x) < logb 3 (1) := by
          apply Real.logb_lt_logb
          all_goals linarith
        have h13 : logb 3 (1) = 0 := by
          rw [logb_one]
        linarith [h13]
      linarith [h6, h10]
    have h10 : x ≤ 2 := by nlinarith
    linarith
  · -- Now prove the reverse: if x = 2, then x in left side
    intro heq
    rw [heq]
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Verify the equation
      have h7 : (3 - (2 : ℝ) : ℝ) > 0 := by norm_num
      have h8 : logb 3 (3 - (2 : ℝ) ) = 0 := by
        rw [show (3 - (2 : ℝ) ) = 1 by norm_num]
        simp
      have h9 : sqrt (sqrt ((2 : ℝ) - 1) - 1 / sqrt ((2 : ℝ) - 1)) = 0 := by
        have h10 : (2 : ℝ) - 1 = 1 := by norm_num
        rw [h10]
        have h11 : sqrt (1 : ℝ) = 1 := by
          rw [Real.sqrt_eq_cases]
          all_goals norm_num
        rw [h11]
        norm_num
        all_goals norm_num
      rw [h8, h9]
      all_goals norm_num