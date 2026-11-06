import Mathlib

theorem number_theory_113479 : IsGreatest {x | ∀ n, x ∣ 7^(n + 2) + 8^(2 * n + 1)} 57 := by
  constructor
  · -- Show that 57 is in the set
    show ∀ n, 57 ∣ 7 ^ (n + 2) + 8 ^ (2 * n + 1)
    intro n
    have h1 : ∀ n : ℕ, (7 ^ (n + 2) + 8 ^ (2 * n + 1) : ℕ) % 57 = 0 := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ k ih =>
        have eq1 : (7 ^ ((k + 1) + 2) + 8 ^ (2 * (k + 1) + 1) : ℕ) =
            (7 * (7 ^ (k + 2)) + 64 * (8 ^ (2 * k + 1)) : ℕ) := by
          ring_nf
        have eq2 : (7 * (7 ^ (k + 2)) + 64 * (8 ^ (2 * k + 1)) : ℕ) % 57 = 0 := by
          have eq3 : (7 ^ (k + 2) + 8 ^ (2 * k + 1) : ℕ) % 57 = 0 := ih
          omega
        rw [eq1]
        exact eq2
    have h8 : (57 ∣ (7 ^ (n + 2) + 8 ^ (2 * n + 1) : ℕ)) := by
      have eq0 : (7 ^ (n + 2) + 8 ^ (2 * n + 1) : ℕ) % 57 = 0 := h1 n
      exact Nat.dvd_of_mod_eq_zero eq0
    exact h8
  · -- Show that 57 is greatest in the set
    intro d hd
    have h2 : ∀ n, d ∣ 7 ^ (n + 2) + 8 ^ (2 * n + 1) := hd
    have h3 := h2 0
    have h4 : d ∣ 57 := by
      norm_num at h3 ⊢
      all_goals try exact h3
    -- Now, from d divides 57, we need to show d ≤ 57
    have h5 : d ≤ 57 := by
      exact Nat.le_of_dvd (by norm_num) h4
    linarith