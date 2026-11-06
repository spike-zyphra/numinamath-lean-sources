import Mathlib

theorem number_theory_188799 (n : ℕ) (hn : n > 5) :
    (5 * n) / (n - 5) = 30 ↔ n = 6 := by 
  constructor 
  · -- Assume (5 * n) / (n - 5) = 30, prove n = 6 
    intro h 
    have h1 : n - 5 > 0 := by 
      omega 
    have h4 : n ≤ 35 := by
      by_contra h11
      push_neg at h11 
      have h5 : (5 * n) / (n - 5) < 30 := by 
        have h6 : n > 35 := h11 
        have h7 : n - 5 > 30 := by 
          omega 
        have h8 : 5 * n < 30 * (n - 5) := by 
          omega 
        have h9 : (5 * n) / (n - 5) < 30 := by 
          apply Nat.div_lt_of_lt_mul 
          all_goals omega 
        exact_mod_cast h9 
      omega 
    have h9 : n ≥ 6 := by 
      by_contra h11 
      push_neg at h11 
      have h12 : n < 6 := by 
        omega 
      omega 
    have h10 : n = 6 := by
      interval_cases n <;> omega 
    exact_mod_cast h10 
  · -- Assume n = 6 prove (5 * n) / (n - 5) = 30 
    intro h 
    rw [h] 
    all_goals norm_num