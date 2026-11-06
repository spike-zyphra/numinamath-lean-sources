import Mathlib

theorem algebra_1764 (x y : ℤ) : 5 * x ^ 2 - 4 * x * y + y ^ 2 = 10 * x - 20 ↔ (x, y) = (6, 10) ∨ (x, y) = (6, 14) ∨ (x, y) = (4, 6) ∨ (x, y) = (4, 10) ∨ (x, y) = (7, 13) ∨ (x, y) = (7, 15) ∨ (x, y) = (3, 5) ∨ (x, y) = (3, 7):= by
  constructor
  · -- Assume the equation holds, prove the pairs
    intro h
    have h1 : x ≥ 3 := by
      nlinarith [sq_nonneg (y - 2 * x), sq_nonneg (x - 5), sq_nonneg (x - 3), sq_nonneg (x - 7)]
    have h2 : x ≤ 7 := by
      nlinarith [sq_nonneg (y - 2 * x), sq_nonneg (x - 5), sq_nonneg (x - 3), sq_nonneg (x - 7)]
    interval_cases x <;> try { 
      omega 
    } <;> try { 
      have h2 : y ≤ 20 := by 
        nlinarith 
      have h3 : y ≥ -20 := by 
        nlinarith 
      interval_cases y <;> 
        simp [Prod.ext_iff] at h ⊢ 
    }
    all_goals omega
  · -- Prove the converse
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ )
    · -- Check (6, 10)
      norm_num
    · -- Check (6, 14)
      norm_num
    · -- Check (4, 6)
      norm_num
    · -- Check (4, 10)
      norm_num
    · -- Check (7, 13)
      norm_num
    · -- Check (7, 15)
      norm_num
    · -- Check (3, 5)
      norm_num
    · -- Check (3, 7)
      norm_num