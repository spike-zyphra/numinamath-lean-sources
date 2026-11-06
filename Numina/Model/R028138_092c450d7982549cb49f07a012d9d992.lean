import Mathlib

theorem number_theory_28840 (n : ℕ) (hn : n > 0) :
    ¬ ∃ m, m^2 = 2551 * 543^n - 2008 * 7^n := by 
  rintro ⟨m, hm⟩ 
  have h11 : (2551 * 543^n - 2008 * 7^n) % 3 = 2 := by 
    have h2 : ∀ n : ℕ, n > 0 → (2551 * 543^n - 2008 * 7^n : ℕ) % 3 = 2 := by 
      intro n hn
      induction n with 
      | zero => 
        linarith 
      | succ n ih => 
        cases n with 
        | zero => 
          norm_num at ih ⊢ 
        | succ n => 
          simp [Nat.pow_succ, Nat.mul_mod, Nat.pow_zero] at ih ⊢ 
          all_goals omega 
    specialize h2 n hn 
    assumption 
  -- Show that a square modulo 3 can only be 0 or 1
  have h3 : m^2 % 3 = 0 ∨ m^2 % 3 = 1 := by
    have h4 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by 
      omega 
    rcases h4 with (h | h | h) <;> 
      simp [pow_two, Nat.mul_mod, h]
  -- Relate m^2 with the expression 
  have h4 : m^2 % 3 = (2551 * 543^n - 2008 * 7^n) % 3 := by 
    omega 
  -- Now it is a contradiction from h11 and h4, h3.
  omega