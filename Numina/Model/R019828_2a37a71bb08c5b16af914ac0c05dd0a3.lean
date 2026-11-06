import Mathlib

theorem algebra_107735
    (a : ℕ → ℝ)
    (h₀ : a 0 = 1)
    (h₁ : a 1 = 5)
    (h₂ : ∀ n, a (n + 2) = (2 * (a (n + 1))^2 - 3 * a (n + 1) - 9) / (2 * a n)) :
    ∀ n, a n = 2^(n + 2) - 3 := by 
  intro n 
  have h3 : ∀ (n : ℕ), a n = 2 ^ (n + 2) - 3 := by
    intro n 
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      simp [h₀]
      all_goals norm_num 
    | succ n =>
      cases n with
      | zero =>
        simp [h₁]
        all_goals norm_num 
      | succ n =>
        have h4 := ih (n) (by linarith)
        have h5 := ih (n + 1) (by linarith)
        have h6 : a (n + 2) = (2 * (a (n + 1))^2 - 3 * a (n + 1) - 9) / (2 * a n) := by 
          specialize h₂ n 
          simpa using h₂ 
        rw [h6]
        rw [h5]
        rw [h4]
        field_simp [(show (2 : ℝ) ^ (n + 2) - 3 ≠ 0 by
          by_contra h
          have h7 : (2 : ℝ) ^ (n + 2) = 3 := by linarith 
          have h8 : (2 : ℝ) ^ (n + 2) > 0 := by positivity 
          have h9 : (2 : ℝ) ^ (n + 2) ≥ 4 := by 
            have h10 : (n + 2 : ℕ) ≥ (2 : ℕ) := by 
              omega 
            have h11 : (2 : ℝ) ^ (n + 2 : ℕ) ≥ (2 : ℝ) ^ (2 : ℕ) := by 
              apply pow_le_pow_right 
              all_goals norm_num 
              all_goals omega 
            norm_num at h11 ⊢ 
            linarith 
          linarith 
        )
        ]
        ring_nf
        <;> norm_num 
        <;> ring_nf 
        <;> norm_num 
  specialize h3 n 
  simpa using h3