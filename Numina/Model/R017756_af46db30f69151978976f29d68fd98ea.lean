import Mathlib

theorem algebra_223864 {a : ℝ} (ha : a ≠ 0) (h : ∃ n : ℤ, a + 1 / a = n) :
    ∃ m : ℤ, a ^ 2 + 1 / a ^ 2 = m ∧ ∀ n : ℕ, ∃ k : ℤ, a ^ n + 1 / a ^ n = k := by
  rcases h with ⟨m, hm⟩
  use m ^ 2 - 2
  constructor
  · -- Show that a^2 + 1/a^2 = m^2 - 2.
    have h1 : a ^ 2 + 1 / a ^ 2 = (a + 1 / a) ^ 2 - 2 := by
      field_simp
      ring
    rw [h1, hm]
    all_goals norm_num
  · -- Show that ∀ n : ℕ, ∃ k : ℤ, a ^ n + 1 / a ^ n = k
    intro n
    have h30 : ∀ n : ℕ, ∃ k : ℤ, a ^ n + 1 / a ^ n = k := by
      intro n
      induction' n using Nat.strongRecOn with n ih
      cases n with
      | zero =>
        use 2
        norm_num
      | succ n =>
        cases n with
        | zero =>
          use m
          all_goals
          simpa using hm
        | succ n =>
          have h10 := ih n (by linarith)
          have h11 := ih (n + 1) (by linarith)
          rcases h10 with ⟨k, hk⟩
          rcases h11 with ⟨l, hl⟩
          have eq1 : a ^ (n + 2 : ℕ) + 1 / a ^ (n + 2 : ℕ) = (a + 1 / a) * (a ^ (n + 1 : ℕ) + 1 / a ^ (n + 1 : ℕ)) - (a ^ (n : ℕ) + 1 / a ^ (n : ℕ)) := by
            field_simp at *
            ring
          rw [eq1, hm, hl, hk]
          refine' ⟨m * l - k, by norm_num⟩
    specialize h30 n
    simpa using h30