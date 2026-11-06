import Mathlib

theorem number_theory_233452 : ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = 1986 ^ 1986 + 1990 ^ 1990 := by
  use 2
  use (1986 ^ 1986 + 1990 ^ 1990) / 2
  constructor
  · -- Show that 1 < 2
    norm_num
  constructor
  · -- Show that 1 < (1986 ^ 1986 + 1990 ^ 1990) / 2
    have h1 : 1986 ^ 1986 + 1990 ^ 1990 > 4 := by
      have h2 : 1986 ^ 1986 ≥ 1986 := by
        have h3 : 1986 ^ 1986 ≥ 1986 ^ 1 := by 
          apply Nat.pow_le_pow_of_le_right
          all_goals norm_num
        have h4 : 1986 ^ 1 = 1986 := by norm_num
        have h5 : 1986 ^ 1986 ≥ 1986 := by 
          rw [h4] at h3
          exact h3
        exact_mod_cast h5
      have h3 : 1990 ^ 1990 ≥ 1990 := by
        have h4 : 1990 ^ 1990 ≥ 1990 ^ 1 := by 
          apply Nat.pow_le_pow_of_le_right 
          all_goals norm_num
        have h5 : 1990 ^ 1 = 1990 := by norm_num
        have h6 : 1990 ^ 1990 ≥ 1990 := by 
          rw [h5] at h4 
          exact h4 
        exact_mod_cast h6
      omega
    omega
  · -- Show that 2 * ((1986 ^ 1986 + 1990 ^ 1990) / 2) = 1986 ^ 1986 + 1990 ^ 1990
    have h1 : (1986 ^ 1986 + 1990 ^ 1990) % 2 = 0 := by
      have h2 : (1986 ^ 1986) % 2 = 0 := by
        have h5 : ∀ (n : ℕ), (1986 ^ (n + 1)) % 2 = 0 := by 
          intro n
          induction n with 
          | zero =>
            norm_num 
          | succ n ih =>
            have h1986 : 1986 % 2 = 0 := by norm_num 
            have eq1 : 1986 ^ (n + 1 + 1) = 1986 * (1986 ^ (n + 1)) := by 
              ring 
            rw [eq1]
            simp [Nat.mul_mod, h1986] at ih ⊢ 
            all_goals omega 
        specialize h5 1985
        simpa using h5 
      have h4' : (1990 ^ 1990) % 2 = 0 := by
        have h6 : ∀ (n : ℕ), (1990 ^ (n + 1)) % 2 = 0 := by
          intro n 
          induction n with
          | zero =>
            norm_num 
          | succ n ih => 
            have h1990 : 1990 % 2 = 0 := by norm_num 
            have eq1 : 1990 ^ (n + 1 + 1) = 1990 * (1990 ^ (n + 1)) := by 
              ring 
            rw [eq1]
            simp [Nat.mul_mod, h1990] at ih ⊢ 
            all_goals omega 
        specialize h6 1989
        simpa using h6 
      omega
    omega