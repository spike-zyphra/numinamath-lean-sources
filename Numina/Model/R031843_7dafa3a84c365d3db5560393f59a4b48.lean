import Mathlib

theorem algebra_11778 {x : ℕ} (h : 64^5 = 32^x) : (2 : ℚ)^(-x : ℤ) = 1 / 64 := by 
  have h1 : x = 6 := by
    have h2 : (64 ^ 5 : ℕ) = (2 ^ 30 : ℕ) := by
      norm_num
    have h3 : (32 ^ x : ℕ) = (2 ^ (5 * x : ℕ) : ℕ) := by
      have h4 : ∀ x : ℕ, (32 ^ x : ℕ) = (2 ^ (5 * x : ℕ) : ℕ) := by
        intro x 
        induction x with
        | zero => 
          simp
        | succ x ih =>
          simp [pow_succ, pow_mul] at ih ⊢
          <;> ring_nf at ih ⊢ <;> try omega
          all_goals try tauto
      specialize h4 x 
      simpa using h4 
    -- Now equate the two expressions via the original hypothesis.
    have h5 : (2 : ℕ) ^ (30 : ℕ) = (2 : ℕ) ^ (5 * x : ℕ) := by
      have h6 : (64 ^ 5 : ℕ) = (32 ^ x : ℕ) := by 
        exact_mod_cast h
      rw [show (64 ^ 5 : ℕ) = (2 ^ 30 : ℕ) by exact_mod_cast h2] at h6
      rw [show (32 ^ x : ℕ) = (2 ^ (5 * x : ℕ) : ℕ) by exact_mod_cast h3] at h6
      all_goals try tauto 
      all_goals try linarith 
    -- Now that we have 2^30 = 2^(5*x), we can equate the exponents.
    have h6 : (30 : ℕ) = (5 * x : ℕ) := by 
      exact Nat.pow_right_injective (by norm_num) h5
    -- Solve for x.
    have h7 : x = 6 := by 
      omega 
    exact_mod_cast h7 
  rw [h1] 
  norm_num