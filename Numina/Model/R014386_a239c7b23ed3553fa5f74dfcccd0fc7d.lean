import Mathlib

theorem algebra_103350 {x : ℝ} (hx : x ≠ 0) (h : ∃ n : ℤ, x + 1 / x = n) :
    ∀ n : ℕ, ∃ m : ℤ, x ^ n + 1 / x ^ n = m := by
  intro n
  have h2 : ∀ (n : ℕ), ∃ m : ℤ, x ^ n + 1 / x ^ n = m := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      use 2
      field_simp at *
      <;> norm_num
      <;> nlinarith
    | succ n =>
      cases n with
      | zero =>
        rcases h with ⟨n₀, hn⟩
        use n₀
        field_simp at hn ⊢
        <;> nlinarith
      | succ n =>
        have h₁ := ih (n) (by linarith)
        have h₂ := ih (n + 1) (by linarith)
        rcases h₁ with ⟨m₁, hm₁⟩
        rcases h₂ with ⟨m₂, hm₂⟩
        rcases h with ⟨n₀, hn₀⟩
        use n₀ * m₂ - m₁
        have h3 : x ^ (n + 2) + 1 / x ^ (n + 2) = (x + 1 / x) * (x ^ (n + 1) + 1 / x ^ (n + 1)) - (x ^ n + 1 / x ^ n) := by
          field_simp
          <;> ring
        rw [h3, hn₀, hm₂, hm₁]
        all_goals norm_num
        all_goals nlinarith
  specialize h2 n
  simpa using h2