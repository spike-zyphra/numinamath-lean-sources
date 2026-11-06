import Mathlib

theorem number_theory_298127 (a : ℕ → ℤ)
    (h₀ : a 0 = 0)
    (h₁ : a 1 = 1)
    (h₂ : ∀ n > 0, a (n + 1) = 2 * a n + 2013 * a (n - 1)) :
    IsLeast {n | 0 < n ∧ 2014 ∣ a n} 2014 := by
  have h3 : ∀ (n : ℕ), a n % 2014 = n % 2014 := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      simp [h₀]
      <;> omega
    | succ n =>
      cases n with
      | zero =>
        simp [h₁]
        <;> omega
      | succ n =>
        have h4 := h₂ (n+1) (by omega)
        simp [show n + 1 + 1 = n + 2 by omega] at h4 ⊢
        have h5 := ih (n + 1) (by omega)
        have h6 := ih (n) (by omega)
        omega
  constructor
  · -- Show that 2014 is in the set
    constructor
    · -- Show that 2014 > 0
      norm_num
    · -- Show that 2014 divides a 2014
      have h4 : a 2014 % 2014 = 2014 % 2014 := by
        apply h3
      norm_num at h4 ⊢
      all_goals omega
  · -- Show that 2014 is the smallest element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    have h4 : n < 2014 := h
    have h5 : a n % 2014 = n % 2014 := by
      apply h3
    have h6 : a n % 2014 = 0 := by 
      omega
    have h7 : n % 2014 = 0 := by 
      omega
    interval_cases n <;> omega