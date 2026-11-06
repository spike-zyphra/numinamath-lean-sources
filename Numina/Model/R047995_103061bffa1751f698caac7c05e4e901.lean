import Mathlib

theorem algebra_607535 : {(a, b) : ℤ × ℤ | (a + 1) * (b - 1) = a ^ 2 * b ^ 2} = {(0, 1), (-1, 0)} := by
  ext ⟨a, b⟩ 
  simp
  constructor 
  · -- Assume h : (a + 1) * (b - 1) = a ^ 2 * b ^ 2, prove (a, b) = (0, 1) ∨ (a, b) = (-1, 0)
    rintro h
    have h1 : a ≤ 1 := by 
      by_contra h1 
      push_neg at h1 
      have h2 : b ≥ 0 := by nlinarith [sq_nonneg (a * b), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a * (b - 1)), sq_nonneg ((a + 1) * b)]
      by_cases h3 : b > 1 
      · -- If b > 1 
        nlinarith [sq_nonneg ((a * b) ^ 2), sq_nonneg ((a + 1) * (b - 1)), sq_nonneg ((a - 1) * (b - 1)), mul_pos (show 0 < a by nlinarith) (show 0 < b by nlinarith), sq_nonneg (a * b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1)]
      · -- If b ≤ 1 
        have h5 : b = 0 ∨ b = 1 := by 
          interval_cases b <;> try { tauto }
        rcases h5 with (h5 | h5) 
        · -- If b = 0 
          rw [show b = 0 by linarith] at h 
          nlinarith [sq_nonneg (a ^ 2 - 1)]
        · -- If b = 1 
          rw [show b = 1 by linarith] at h 
          nlinarith [sq_nonneg (a ^ 2 - 1)]
    have h2 : a ≥ -1 := by
      by_contra h2 
      push_neg at h2 
      have h3 : b ≤ 0 := by 
        nlinarith [sq_nonneg (a * b), sq_nonneg (a + 1), sq_nonneg (b - 1), sq_nonneg (a * (b - 1)), sq_nonneg ((a + 1) * b)]
      by_cases h4 : b < 0 
      · -- If b < 0 
        nlinarith [sq_nonneg ((a * b) ^ 2), sq_nonneg ((a + 1) * (b - 1)), sq_nonneg ((a + 1) * (b + 1)), mul_pos (show 0 < -a by nlinarith) (show 0 < -b by nlinarith), sq_nonneg (a * b + 1), sq_nonneg (a + 1), sq_nonneg (b + 1)]
      · -- If b ≥ 0 
        have h6 : b = 0 := by 
          nlinarith 
        rw [show b = 0 by linarith] at h 
        nlinarith [sq_nonneg (a + 1)]
    interval_cases a <;> 
      try { 
        have h5 : b ≤ 2 := by nlinarith [sq_nonneg (b ^ 2 - 1)]
        have h6 : b ≥ -2 := by nlinarith [sq_nonneg (b ^ 2 - 1)]
        interval_cases b <;> tauto 
      }
      <;> try { 
        all_goals 
          nlinarith 
      }
  · -- Reverse implication: if (a,b) in {(0,1), (-1,0)}, then (a+1)(b-1) = a^2 b^2
    rintro (h | h)
    · -- (0, 1)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (-1, 0)
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num