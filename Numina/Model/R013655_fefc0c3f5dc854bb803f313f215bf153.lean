import Mathlib

theorem number_theory_106477 (n : ℕ) :
    (n + 1) ∣ (n ^ 2 + 1) ↔ n = 0 ∨ n = 1 := by
  constructor
  · -- Assume h: n + 1 divides n ^ 2 + 1, prove n = 0 ∨ n = 1
    intro h
    by_cases hn : n = 0
    · -- Assume n = 0 
      simp [hn] 
    · -- Assume n ≠ 0 
      have h1 : (n + 1) ∣ 2 := by 
        have h2 : (n + 1) ∣ (n ^ 2 + 1) := h 
        have h3 : (n + 1) ∣ (n + 1) * (n) := by 
          apply dvd_mul_right 
        have h4 : (n + 1) ∣ ((n + 1) * (n) - (n ^ 2 + 1)) := by 
          apply Nat.dvd_sub' 
          · exact h3 
          · exact h2 
        have eq1 : ((n + 1) * (n) - (n ^ 2 + 1)) = (n - 1) := by 
          cases n with 
          | zero => 
            all_goals 
            simp [hn] 
          | succ n => 
            simp [Nat.add_assoc, Nat.mul_succ, Nat.mul_comm]
            <;> ring_nf 
            <;> omega 
        rw [eq1] at h4 
        have h5 : (n + 1) ∣ (n + 1) := by 
          use 1 
          all_goals 
          simp 
        have h6 : (n + 1) ∣ ((n + 1) - (n - 1) ) := by 
          apply Nat.dvd_sub' 
          · exact h5 
          · exact h4 
        -- Now show that ((n + 1) - (n - 1) ) = 2 when n ≥ 1
        have h7 : n ≥ 1 := by 
          by_contra h
          push_neg at h
          have : n = 0 := by 
            omega 
          tauto 
        have eq2 : ((n + 1) - (n - 1) ) = 2 := by 
          have eq3 : n ≥ 1 := h7 
          have eq4 : n + 1 = (n - 1) + 2 := by 
            omega 
          have eq5 : (n + 1) - (n - 1) = 2 := by 
            omega 
          exact_mod_cast eq5 
        rw [eq2] at h6 
        exact_mod_cast h6 
      have h2 : (n + 1) ≤ 2 := by 
        exact Nat.le_of_dvd (by norm_num) h1 
      have h3 : n ≤ 1 := by 
        omega 
      have h4 : n = 1 := by 
        have hn5 : n > 0 := by 
          by_contra h 
          push_neg at h 
          have hn6 : n = 0 := by 
            omega 
          omega 
        have hn6 : n > 0 := hn5 
        have hn7 : n ≥ 1 := by 
          omega 
        have hn8 : n ≤ 1 := by 
          omega 
        have hn9 : n = 1 := by 
          omega 
        exact_mod_cast hn9 
      right 
      exact_mod_cast h4 
  · -- Backward direction: n = 0 ∨ n = 1 → n + 1 ∣ n^ 2 + 1 
    rintro (h | h)
    · -- Case n = 0 
      rw [h] 
      all_goals 
      norm_num 
    · -- Case n = 1 
      rw [h] 
      all_goals 
      norm_num