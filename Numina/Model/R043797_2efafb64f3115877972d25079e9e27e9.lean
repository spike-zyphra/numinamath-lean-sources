import Mathlib

theorem number_theory_260350 {n : ℕ} (hn : ∃ m, n = m^2) :
    ∃ p, n % 16 = p^2 := by 
  rcases hn with ⟨m, rfl⟩
  have h1 : m^2 % 16 = 0 ∨ m^2 % 16 = 1 ∨ m^2 % 16 = 4 ∨ m^2 % 16 = 9 := by 
    have h1 : m % 16 = 0 ∨ m % 16 = 1 ∨ m % 16 = 2 ∨ m % 16 = 3 ∨ m % 16 = 4 ∨ m % 16 = 5 ∨ m % 16 = 6 ∨ m % 16 = 7 ∨ m % 16 = 8 ∨ m % 16 = 9 ∨ m % 16 = 10 ∨ m % 16 = 11 ∨ m % 16 = 12 ∨ m % 16 = 13 ∨ m % 16 = 14 ∨ m % 16 = 15 := by
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [Nat.pow_mod, h1]
  rcases h1 with (h | h | h | h)
  · -- case m^2 % 16 = 0 
    use 0 
    all_goals 
    omega 
  · -- case m^2 % 16 = 1 
    use 1 
    all_goals 
    omega 
  · -- case m^2 % 16 = 4 
    use 2 
    all_goals 
    omega 
  · -- case m^2 % 16 = 9 
    use 3 
    all_goals 
    omega