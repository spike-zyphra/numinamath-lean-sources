import Mathlib

theorem number_theory_115475 (a : ℕ → ℤ)
    (h₀ : a 0 = 0)
    (h₁ : a 1 = 1)
    (h₂ : ∀ n > 0, a (n + 1) = 2 * a n + 2007 * a (n - 1)) :
    IsLeast {n | 0 < n ∧ 2008 ∣ a n} 2008 := by

  have h3 : ∀ (n : ℕ), a n % 2008 = (n : ℤ) % 2008 := by
    intro n 
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      simp [h₀]
    | succ n =>
      cases n with
      | zero =>
        simp [h₁]
      | succ n =>
        have eq1 := ih (n) (by linarith)
        have eq2 := ih (n + 1) (by linarith)
        have h4 : a (n + 2) = 2 * a (n + 1) + 2007 * a n := by
          specialize h₂ (n + 1) (by linarith)
          simpa using h₂
        have : a (n + 2) % 2008 = (↑(n + 2) : ℤ) % 2008 := by
          simp [h4, Int.add_emod, Int.mul_emod, eq1, eq2] at *
          all_goals omega
        simpa using this

  constructor
  · -- Show 2008 is in the set
    constructor 
    · -- Show 2008 > 0 
      norm_num 
    · -- Show 2008 divides a_2008
      have h4 : a 2008 % 2008 = 0 := by 
        have h5 : ∀ (n : ℕ), a n % 2008 = (n : ℤ) % 2008 := h3 
        specialize h5 2008 
        norm_num at h5 ⊢ 
        all_goals 
          omega 
      omega
  · -- Show minimality 
    intro n hn 
    rcases hn with ⟨hn_pos, hn_div⟩ 
    have h4 : a n % 2008 = 0 := by 
      omega 
    have h5 : n % 2008 = 0 := by 
      have eq1 : a n % 2008 = (n : ℤ) % 2008 := h3 n 
      omega 
    by_contra h 
    push_neg at h 
    have h6 : n < 2008 := by linarith 
    omega