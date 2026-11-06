import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_190295 (x : ℝ) (hx : 0 < x) :
    (logb 0.5 x)^2 + logb 0.5 x - 2 ≤ 0 ↔ 0.5 ≤ x ∧ x ≤ 4 := by
  have h1 : logb 0.5 x = -logb 2 x := by
    have h2 : logb 0.5 x = logb 2 x / logb 2 (0.5 : ℝ) := by
      field_simp [logb]
    have h3 : logb 2 (0.5 : ℝ) = -1 := by
      rw [show (0.5 : ℝ) = (1 / 2 : ℝ) by norm_num]
      simp [logb_div, logb_one]
    rw [h2, h3]
    all_goals ring
  rw [h1]
  constructor
  · -- Assume (logb 0.5 x)^2 + logb 0.5 x - 2 ≤ 0, prove 0.5 ≤ x ∧ x ≤ 4
    intro h
    have h2 : (logb 2 x) ^ 2 - logb 2 x - 2 ≤ 0 := by nlinarith
    have h3 : -1 ≤ logb 2 x ∧ logb 2 x ≤ 2 := by
      constructor
      · -- Prove -1 ≤ logb 2 x
        nlinarith 
      · -- Prove logb 2 x ≤ 2
        nlinarith 
    have h4 : (0.5 : ℝ) ≤ x := by
      have h5 : (2 : ℝ) ^ (-1 : ℝ) ≤ x := by
        have h11 : logb (2 : ℝ) ((2 : ℝ) ^ (-1 : ℝ)) = -1 := by 
          rw [logb_rpow]
          all_goals norm_num
        have h12 : logb (2 : ℝ) x ≥ -1 := by linarith [h3.1]
        have h13 : (2 : ℝ) ^ (-1 : ℝ) ≤ x := by
          by_contra h
          push_neg at h
          have h14 : logb (2 : ℝ) x < logb (2 : ℝ) ((2 : ℝ) ^ (-1 : ℝ)) := by
            apply Real.logb_lt_logb
            all_goals
              try { norm_num  }
              try { linarith [show (0 : ℝ) < (2 : ℝ) by norm_num, show (2 : ℝ) ^ (-1 : ℝ) > 0 by positivity, h]  }
          linarith [h11, h14, h12]
        linarith
      have h7 : (2 : ℝ) ^ (-1 : ℝ) = (0.5 : ℝ) := by
        norm_num
      rw [h7] at h5
      linarith
    have h8 : x ≤ (4 : ℝ) := by
      have h9 : x ≤ (2 : ℝ) ^ (2 : ℝ) := by
        have h14 : logb (2 : ℝ) x ≤ (2 : ℝ) := by linarith [h3.2]
        have h10 : logb (2 : ℝ) ((2 : ℝ) ^ (2 : ℝ)) = (2 : ℝ) := by 
          rw [logb_rpow]
          all_goals norm_num
        have h11 : x ≤ (2 : ℝ) ^ (2 : ℝ) := by
          by_contra h
          push_neg at h
          have h12 : logb (2 : ℝ) x > logb (2 : ℝ) ((2 : ℝ) ^ (2 : ℝ)) := by
            apply Real.logb_lt_logb
            all_goals
              try { norm_num  }
              try { linarith [show (0 : ℝ) < (2 : ℝ) by norm_num, show (2 : ℝ) ^ (2 : ℝ) > 0 by positivity, h]  }
          linarith [h10, h12, h14]
        linarith
      have h15 : (2 : ℝ) ^ (2 : ℝ) = (4 : ℝ) := by
        norm_num
      linarith [h15, h9]
    constructor
    · linarith 
    · linarith
  · -- Assume 0.5 ≤ x ∧ x ≤ 4, prove (logb 0.5 x)^2 + logb 0.5 x - 2 ≤ 0
    rintro ⟨hx1, hx2⟩
    have h3 : -1 ≤ logb 2 x := by
      have h6 : (0.5 : ℝ) ≤ x := by linarith
      have h7 : logb (2 : ℝ) (0.5 : ℝ) ≤ logb (2 : ℝ) x := by
        apply Real.logb_le_logb_of_le
        all_goals
          try { norm_num  }
          try { linarith [show (0.5 : ℝ) ≥ 0 by linarith, show x ≥ 0 by linarith]  }
      have h8 : logb (2 : ℝ) (0.5 : ℝ) = -1 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      nlinarith
    have h9 : logb 2 x ≤ 2 := by
      have h10 : logb (2 : ℝ) x ≤ logb (2 : ℝ) (4 : ℝ) := by
        apply Real.logb_le_logb_of_le
        all_goals
          try { norm_num  }
          try { linarith [show x ≥ 0 by linarith, show (4 : ℝ) ≥ 0 by linarith]  }
      have h11 : logb (2 : ℝ) (4 : ℝ) = 2 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      nlinarith
    nlinarith [sq_nonneg (logb 2 x - 2 : ℝ), sq_nonneg (logb 2 x + 1 : ℝ)]