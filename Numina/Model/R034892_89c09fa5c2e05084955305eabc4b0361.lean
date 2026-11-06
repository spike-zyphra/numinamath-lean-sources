import Mathlib

theorem algebra_302876 (a : ℤ) :
    (∃ x1 x2 : ℤ, (a + 1) * x1 ^ 2 - (a ^ 2 + 1) * x1 + 2 * a ^ 3 - 6 = 0 ∧
      (a + 1) * x2 ^ 2 - (a ^ 2 + 1) * x2 + 2 * a ^ 3 - 6 = 0) ↔ a = -1 ∨ a = 0 ∨ a = 1 := by
  constructor
  · -- Assume there exist integer roots x1, x2
    rintro ⟨x1, x2, h1, h2⟩
    
    ring_nf at h1
    -- prvo derivations
    have h6 : a ≤ 2 := by
      nlinarith [sq_nonneg (x1 + 4), sq_nonneg (x1 - 3), sq_nonneg (x1 + 2), sq_nonneg (x1 - 2), sq_nonneg (x1 - a), sq_nonneg (x1 + 1), sq_nonneg (a + 1), sq_nonneg (a * x1), sq_nonneg (a * (x1 - 2)), sq_nonneg ((x1 - 3) * (x1 + 4)), sq_nonneg ((a + 1) * (x1 - 2))]
    
    have h7 : a ≥ -3 := by
      nlinarith [sq_nonneg (x1 + 4), sq_nonneg (x1 - 3), sq_nonneg (x1 + 2), sq_nonneg (x1 - 2), sq_nonneg (x1 - a), sq_nonneg (x1 + 1), sq_nonneg (a + 1), sq_nonneg (a * x1), sq_nonneg (a * (x1 - 2)), sq_nonneg ((x1 - 3) * (x1 + 4)), sq_nonneg ((a + 1) * (x1 - 2))]
    
    interval_cases a <;> try { 
      omega 
    }
    <;> try { 
      have h8 : x1 ≤ 7 := by
        nlinarith 
      have h9 : x1 ≥ -4 := by
        nlinarith 
      interval_cases x1 <;> omega 
    }
  · -- Assume a = -1 or a = 0 or a = 1
    rintro (h | h | h)
    · -- a = -1
      rw [h]
      use -4, -4
      all_goals
        norm_num
    · -- a = 0
      rw [h]
      use 3, 3
      all_goals
        norm_num
    · -- a = 1
      rw [h]
      use 2, 2
      all_goals
        norm_num