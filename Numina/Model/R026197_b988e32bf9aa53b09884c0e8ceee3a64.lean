import Mathlib

theorem number_theory_321995 (a : ℕ → ℤ)
    (h₀ : a 0 = 0)
    (h₁ : a 1 = 1)
    (h₂ : ∀ n > 0, a (n + 1) = 2 * a n + 2007 * a (n - 1)) :
    IsLeast {n | 0 < n ∧ 2008 ∣ a n} 2008 := by

  have h3 : ∀ n : ℕ, a n % 2008 = n % 2008 := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      -- n = 0
      simp [h₀]
    | succ n =>
      cases n with
      | zero =>
        -- n = 1
        simp [h₁]
      | succ n =>
        -- n = n + 2
        have eq3 := h₂ (n + 1) (by linarith)
        simp [show n + 1 + 1 = n + 2 by omega] at eq3 ⊢
        have eq1 := ih (n) (by linarith)
        have eq2 := ih (n + 1) (by linarith)
        simp [eq3, eq1, eq2, Int.add_emod, Int.mul_emod, Int.sub_emod]
        <;> omega

  constructor
  · -- Show that 2008 is in the set
    constructor
    · -- Show that 2008 > 0
      norm_num
    · -- Show that 2008 divides a 2008
      have h4 : 2008 ∣ a 2008 := by
        have h5 : a 2008 % 2008 = 2008 % 2008 := h3 2008
        omega
      exact h4
  · -- Show that 2008 is minimal
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    have h4 : a n % 2008 = n % 2008 := h3 n
    have h5 : n % 2008 = 0 := by
      omega
    omega