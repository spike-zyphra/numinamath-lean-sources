import Mathlib

theorem algebra_285071 (f : ℕ → ℚ) (h1 : f 1 = 3 / 2)
    (h2 : ∀ x y, f (x + y) = (1 + y / (x + 1)) * f x + (1 + x / (y + 1)) * f y +
      x ^ 2 * y + x * y + x * y ^ 2) : f 20 = 4305 := by

  have h3 : ∀ (n : ℕ), f n = ( ((n : ℚ) * ( (n : ℚ) + 1 ) * (2 * (n : ℚ) + 1 )) / 4 ) := by
    intro n 
    induction' n using Nat.strongRecOn with n ih 
    cases n with 
    | zero =>
      have h0 : f 0 = 0 := by 
        specialize h2 0 0 
        norm_num at h2 
        linarith 
      simp [h0]
    | succ n => 
      cases n with 
      | zero => 
        norm_num at *
        all_goals 
          try tauto 
          <;> linarith [h1]
      | succ n => 
        have eq1a : f (n + 1 + 1) = (1 + 1 / (↑(n + 1) + 1)) * f (n + 1) + (1 + (↑(n + 1) : ℚ) / 2) * f 1 + (↑(n + 1) : ℚ) ^ 2 + (↑(n + 1) : ℚ) + (↑(n + 1) : ℚ) := by 
          specialize h2 (n + 1) 1 
          simp [show (n + 1 + 1 : ℕ) = (n + 1 : ℕ) + (1 : ℕ) by omega] at h2 ⊢ 
          norm_num at h2 ⊢ 
          <;> linarith 
        have eq2 : f (n + 1) = ((↑(n + 1) : ℚ) * ((↑(n + 1) : ℚ) + 1) * (2 * (↑(n + 1) : ℚ) + 1)) / 4 := by 
          apply ih (n + 1) 
          all_goals 
            linarith 
        rw [eq1a] 
        rw [eq2, h1] 
        field_simp at *
        ring_nf 
        all_goals norm_num 
  have h4 := h3 20 
  norm_num at h4 ⊢ 
  linarith