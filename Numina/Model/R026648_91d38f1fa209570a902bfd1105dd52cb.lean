import Mathlib

theorem number_theory_285248 (A B C : ℕ) :
    (A = 2 ∧ B = 4 ∧ C = 2) → ¬(8 ∣ A) ∧ ¬(8 ∣ B) ∧ ¬(8 ∣ C) ∧
    ∀ n : ℕ, 8 ∣ A * 5 ^ n + B * 3 ^ (n - 1) + C := by
  intro h
  rcases h with ⟨ha, hb, hc⟩
  constructor
  · -- Show that 8 does not divide A
    rw [ha]
    omega
  constructor
  · -- Show that 8 does not divide B
    rw [hb]
    omega
  constructor
  · -- Show that 8 does not divide C
    rw [hc]
    omega
  · -- Show that the expression is divisible by 8 for all natural n
    intro n
    rw [ha, hb, hc]
    have h1 : ∀ (n : ℕ), 8 ∣ 2 * 5 ^ n + 4 * 3 ^ (n - 1) + 2 := by
      intro n
      induction' n using Nat.strongRecOn with n ih
      cases n with
      | zero =>
        norm_num
      | succ n =>
        cases n with
        | zero =>
          norm_num
        | succ n =>
          have h2 := ih (n + 1) (by linarith)
          have h3 := ih (n) (by linarith)
          cases n with
          | zero =>
            norm_num at h2 h3 ⊢
            all_goals omega
          | succ n =>
            norm_num [pow_add, pow_mul] at h2 h3 ⊢
            all_goals ring_nf at h2 h3 ⊢
            all_goals omega
    exact h1 n