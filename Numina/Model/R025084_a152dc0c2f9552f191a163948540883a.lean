import Mathlib

theorem algebra_103672 {x : ℝ} (hx : x ≠ 0) (h : ∃ n : ℤ, x + 1/x = n) :
    ∀ n : ℕ, ∃ m : ℤ, x^n + 1/x^n = m := by
  intro n
  have h1 : ∀ (n : ℕ), ∃ m : ℤ, x ^ n + 1 / x ^ n = m := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      use 2
      norm_num
    | succ n =>
      cases n with
      | zero =>
        rcases h with ⟨k, hk⟩
        use k
        field_simp at hk ⊢
        linarith
      | succ n =>
        have h2 := ih n (by linarith)
        have h3 := ih (n + 1) (by linarith)
        rcases h2 with ⟨m, hm⟩
        rcases h3 with ⟨l, hl⟩
        rcases h with ⟨k, hk⟩
        have eq1 : x ^ (n + 2 : ℕ) + 1 / x ^ (n + 2 : ℕ) = (x + 1 / x) * (x ^ (n + 1 : ℕ) + 1 / x ^ (n + 1 : ℕ)) - (x ^ n + 1 / x ^ n) := by
          field_simp
          ring
        rw [eq1, hk, hl, hm]
        refine ⟨k * l - m, by simp⟩
  specialize h1 n
  simpa using h1