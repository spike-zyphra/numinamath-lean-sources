import Mathlib

theorem number_theory_15111 : {x | 15 ∣ x ∧ ∀ y, 15 ∣ y → abs (2009 - y : ℤ) ≥ abs (2009 - x : ℤ)} = {2010} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the set, Show x = 2010
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 := h2 2010 (by norm_num)
    have h4 := h2 1995 (by norm_num)
    have h7 : abs (2009 - x : ℤ) ≤ 1 := by
      norm_num at h3 
      linarith
    have h8 : 2008 ≤ x ∧ x ≤ 2010 := by
      constructor
      · 
        cases' abs_le.mp h7 with h9 h10
        all_goals linarith
      · 
        cases' abs_le.mp h7 with h9 h10
        all_goals linarith
    have h10 : x = 2010 := by
      rcases h8 with ⟨h8a, h8b⟩
      have h11 : x ≤ 2010 := h8b
      have h12 : x ≥ 2008 := h8a
      interval_cases x <;> norm_num at h1 h7 ⊢ <;> tauto
    tauto
  · -- Assume x = 2010, Show x in the set
    intro h
    rw [h]
    constructor
    · -- Show 15 divides 2010
      norm_num
    · -- Show for all y divisible by 15, |2009 - y| >= |2009 - 2010|
      intro y hy
      have h1 : (2009 : ℤ) - (2010 : ℤ) = -1 := by
        norm_num
      have h2 : abs ((2009 : ℤ) - (2010 : ℤ)) = 1 := by
        rw [h1]
        norm_num
      have h3 : abs ((2009 : ℤ) - (y : ℤ)) ≥ 1 := by
        by_contra h
        push_neg at h
        have h5 : (2009 : ℤ) - (y : ℤ) = 0 := by
          have h7 : abs ((2009 : ℤ) - (y : ℤ)) < (1 : ℤ) := by
            simpa using h
          have h8 : (2009 : ℤ) - (y : ℤ) = 0 := by
            cases' abs_cases ((2009 : ℤ) - (y : ℤ)) with h9 h9
            · -- Case |a| = a
              omega
            · -- Case |a| = -a
              omega
          exact h8
        have h6 : (y : ℤ) = 2009 := by
          linarith
        have h7 : (15 : ℤ) ∣ y := by
          simpa using hy
        rw [h6] at h7
        omega
      linarith [h2, h3]