import Mathlib

theorem number_theory_149942 (k : ℕ) (hk : 0 < k) :
    392 ∣ 7^(2 * k) + 343 := by

  -- To prove divisibility by 392, we need divisibility by both 8 and 49.
  -- Prove divisibility by 8
  have h1 : (7 ^ (2 * k) + 343) % 8 = 0 := by 
    have h2 : ∀ k : ℕ, k > 0 → (7 ^ (2 * k) + 343) % 8 = 0 := by 
      intro k hk 
      induction k with 
      | zero => 
        linarith 
      | succ k ih =>
        cases k with 
        | zero => 
          norm_num 
        | succ k =>
          simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢ 
          all_goals 
            omega 
    specialize h2 k hk 
    simpa using h2

  -- Prove divisibility by 49
  have h3 : (7 ^ (2 * k) + 343) % 49 = 0 := by 
    have h4 : ∀ k : ℕ, k > 0 → (7 ^ (2 * k) + 343) % 49 = 0 := by
      intro k hk 
      induction k with 
      | zero => 
        linarith 
      | succ k ih =>
        cases k with 
        | zero => 
          norm_num 
        | succ k =>
          simp [Nat.pow_succ, Nat.pow_mul] at ih ⊢ 
          all_goals 
            omega 
    specialize h4 k hk 
    simpa using h4

  -- Now prove divisibility by 392 using divisibility by 8 and 49
  omega