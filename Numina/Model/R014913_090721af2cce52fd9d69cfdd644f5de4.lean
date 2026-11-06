import Mathlib

theorem algebra_169672 (n : ℕ) :
    ∃ a b : ℤ, n^2 = a + b ∧ n^3 = a^2 + b^2 ↔ n = 0 ∨ n = 1 ∨ n = 2 := by
  by_cases h1 : n ≤ 2 
  · -- n ≤ 2
    have h : n = 0 ∨ n = 1 ∨ n = 2 := by 
      have h1 : n ≤ 2 := h1 
      have h2 : n ≥ 0 := by omega 
      interval_cases n <;> tauto 
    rcases h with (h_eq0 | h_eq1 | h_eq2)
    · -- n = 0 
      use 0, 0 
      simp [h_eq0] 
    · -- n = 1 
      use 0, 1 
      rw [show (n : ℕ) = (1 : ℕ) by omega] 
      all_goals norm_num 
    · -- n = 2 
      use 2, 2 
      rw [show (n : ℕ) = (2 : ℕ) by omega] 
      all_goals norm_num 
  · -- n > 2 
    have h2 : n > 2 := by omega 
    use -1, -1 
    constructor 
    · -- Assume (n ^ 2 = -1 + -1 ∧ n ^ 3 = (-1) ^ 2 + (-1) ^ 2)
      intro h 
      rcases h with ⟨h4, h5⟩
      have h3 : (n : ℤ) > 2 := by 
        exact_mod_cast h2 
      nlinarith 
    · -- Assume (n = 0 ∨ n = 1 ∨ n = 2)
      intro h 
      rcases h with (h | h | h)
      all_goals 
        omega