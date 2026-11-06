import Mathlib

theorem number_theory_177081 (x y : ℕ) : x^3 - y^3 = 999 ↔ (x = 12 ∧ y = 9) ∨ (x = 10 ∧ y = 1) := by
  constructor
  · -- Assume x^3 - y^3 = 999
    intro h
    have h1 : x^3 = y^3 + 999 := by
      omega
    have h11 : x > y := by
      by_contra h3
      push_neg at h3
      have h4 : x ≤ y := by linarith
      have h5 : x^3 ≤ y^3 := by
        have h6 : x ≤ y := h4
        have h7 : x^3 ≤ y^3 := by
          apply Nat.pow_le_pow_of_le_left h6 3
        linarith
      omega
    -- Prove upper bound
    have h2 : x ≤ 22 := by
      by_contra h3
      push_neg at h3
      -- Assume x > 22
      have h40 : y < x := by
        omega
      have h50 : y ≤ 22 := by
        nlinarith [sq_nonneg ((x: Int) - (y: Int) - 3), sq_nonneg ((x: Int) - (y: Int) - 9), sq_nonneg ((x: Int) - 22: Int), sq_nonneg ((y: Int) - 22: Int), sq_nonneg ((y: Int) - 9: Int), sq_nonneg ((y: Int) - 1: Int)]
      have h60 : y ≤ 22 := by
        omega
      have hx10 : x ≤ 22 := by
        nlinarith [sq_nonneg ((x: Int) - (y: Int) - 3), sq_nonneg ((x: Int) - (y: Int) - 9), sq_nonneg ((x: Int) - 22: Int), sq_nonneg ((y: Int) - 22: Int), sq_nonneg ((y: Int) - 9: Int), sq_nonneg ((y: Int) - 1: Int)]
      omega
    -- Prove upper bound for y
    have h70 : y ≤ 22 := by
      nlinarith [sq_nonneg ((x: Int) - (y: Int) - 3), sq_nonneg ((x: Int) - (y: Int) - 9), sq_nonneg ((x: Int) - 22: Int), sq_nonneg ((y: Int) - 22: Int), sq_nonneg ((y: Int) - 9: Int), sq_nonneg ((y: Int) - 1: Int)]
    interval_cases x <;> try { 
      interval_cases y 
      <;> omega 
    } 
    <;> try { 
      omega 
    }
    all_goals
      try { 
        norm_num at h1 
        <;> tauto 
        <;> omega 
      }
      all_goals
      try { 
        omega 
      }
      all_goals
      try { 
        nlinarith 
      }
  · -- Assume (x = 12 ∧ y = 9) ∨ (x = 10 ∧ y = 1)
    rintro (h | h)
    · -- Case (x = 12 ∧ y = 9)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num
    · -- Case (x = 10 ∧ y = 1)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num