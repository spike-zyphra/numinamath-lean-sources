import Mathlib

theorem algebra_10976 {f : ℕ → ℕ → ℕ}
    (h₀ : f 1 1 = 1)
    (h₁ : ∀ m n, 0 < m → 0 < n → f m n > 0)
    (h₂ : ∀ m n, 0 < m → 0 < n → f m (n + 1) = f m n + 2)
    (h₃ : ∀ m n, 0 < m → 0 < n → f (m + 1) 1 = 2 * f m 1) :
    f 2010 2008 = 2 ^ 2009 + 4014 := by

  have eq1 : ∀ (m : ℕ), f (m + 1) 1 = 2 ^ m := by 
    intro m 
    induction m with
    | zero => 
      simp [h₀]
    | succ m ih => 
      have h4 : f (m + 1 + 1) 1 = 2 * f (m + 1) 1 := by 
        apply h₃ (m + 1) 1 
        all_goals 
          simp 
      rw [h4] 
      rw [ih] 
      all_goals 
        ring_nf 
  have eq2 : ∀ (m n : ℕ), f (m + 1) (n + 1) = 2 ^ m + 2 * n := by
    intro m n 
    have eq3 : ∀ (n : ℕ), f (m + 1) (n + 1) = 2 ^ m + 2 * n := by 
      intro n 
      induction n with 
      | zero => 
        simp [eq1 m] 
      | succ n ih => 
        have eq4 : f (m + 1) ((n + 1) + 1) = f (m + 1) (n + 1) + 2 := by 
          specialize h₂ (m + 1) (n + 1) (by linarith) (by linarith)
          simpa using h₂ 
        rw [eq4]
        rw [ih] 
        all_goals 
          simp [Nat.pow_add, Nat.mul_add] 
          <;> ring_nf 
    simpa using eq3 n 
  have eq4 : f 2010 2008 = 2 ^ 2009 + 2 * 2007 := by 
    have h5 : ∀ (m n : ℕ), f (m + 1) (n + 1) = 2 ^ m + 2 * n := eq2 
    specialize h5 2009 2007 
    norm_num at h5 ⊢ 
    linarith 
  norm_num at eq4 ⊢ 
  linarith [eq4]