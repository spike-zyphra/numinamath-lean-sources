import Mathlib

theorem algebra_233051 :
    {n : ℕ | n > 2 ∧ 46800 % n = 0 ∧ 46800 / (n - 2) = 46800 / n + 1950} = {8} := by
  ext n 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n is in the set, so n = 8
    intro h 
    rcases h with ⟨hn2, hdiv, heq⟩
    have h1 : n ≤ 46800 := by 
      by_contra h 
      push_neg at h 
      have h5 : n > 46800 := h 
      have h5' : 46800 % n = 46800 := by 
        rw [Nat.mod_eq_of_lt] 
        all_goals linarith 
      omega 
    by_cases h5 : n ≤ 50 
    · -- Assume n ≤ 50, prove n = 8 
      interval_cases n <;> norm_num at hdiv heq ⊢ 
      <;> omega 
    · -- Assume n > 50, prove contradiction 
      push_neg at h5 
      have h6 : n ≥ 51 := by omega 
      have h7 : n - 2 ≥ 49 := by omega 
      have eq1 : 46800 / (n - 2) = 46800 / n + 1950 := heq 
      have h8 : 46800 / (n - 2) < 46800 / n + 1950 := by 
        have h8a : 46800 / (n - 2) ≤ 955 := by 
          have h12 : n - 2 ≥ 49 := by omega 
          have : 46800 / (n - 2) ≤ 46800 / 49 := by 
            apply Nat.div_le_div_left 
            all_goals omega 
          have : 46800 / 49 = 955 := by norm_num 
          omega 
        have h8b : 46800 / n ≥ 0 := by positivity 
        have h8c : 46800 / (n - 2) < 46800 / n + 1950 := by 
          omega 
        omega 
      omega 
  · -- Assume n = 8, prove n is in the set 
    intro h 
    rw [h] 
    constructor 
    · norm_num 
    constructor 
    · norm_num 
    all_goals norm_num